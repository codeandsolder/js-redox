//! Navigable document-to-module source index for a recovered capture project.
//! Kept independent of runtime evidence: HTML declarations and import edges
//! describe statically reachable code, not necessarily executed functions.
use crate::{
    browser_script_types::is_executable_script,
    capture_project::validate_project_relative_path,
    report_markdown::{code_span, link_destination},
};
use anyhow::Result;
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use work_budget::WorkBudget;

fn fields<'a>(value: &'a Value, key: &str) -> &'a [Value] {
    value
        .get(key)
        .and_then(Value::as_array)
        .map_or_default(Vec::as_slice)
}

fn string<'a>(value: &'a Value, key: &str) -> Option<&'a str> {
    value.get(key).and_then(Value::as_str)
}

fn path_link(unit: &Value, readable: &BTreeMap<&str, &str>) -> String {
    let raw = string(unit, "raw_path");
    let preferred = raw.and_then(|raw| readable.get(raw).copied());
    for path in [preferred, string(unit, "source_path"), raw]
        .into_iter()
        .flatten()
    {
        if validate_project_relative_path(path, "entrypoint source path").is_err() {
            continue;
        }
        // This page is under src/. Non-src paths must be rooted one level up.
        let (label, destination) = path.strip_prefix("src/").map_or_else(
            || (path, format!("../{}", link_destination(path))),
            |relative| (relative, link_destination(relative)),
        );
        return format!("[{}]({destination})", code_span(label));
    }
    format!(
        "{} (no valid project-local source path)",
        code_span(raw.unwrap_or("unknown source"))
    )
}

struct NavigationIndex<'a> {
    js_units: Vec<&'a Value>,
    by_raw: BTreeMap<&'a str, &'a Value>,
    by_url: BTreeMap<&'a str, Vec<&'a Value>>,
    references: BTreeMap<&'a str, &'a [Value]>,
    readable: BTreeMap<&'a str, &'a str>,
}

impl<'a> NavigationIndex<'a> {
    fn new(source_index: &'a Value, deob: &'a Value, references: &'a Value) -> Self {
        let js_units = fields(source_index, "units")
            .iter()
            .filter(|unit| string(unit, "kind") == Some("javascript"))
            .collect::<Vec<_>>();
        let mut by_url = BTreeMap::<&str, Vec<&Value>>::new();
        let mut by_raw = BTreeMap::<&str, &Value>::new();
        for unit in &js_units {
            // Inline script bodies share their document URL but must not be treated
            // as importable modules at that URL.
            if string(unit, "origin") != Some("inline_script") {
                if let Some(url) = string(unit, "url") {
                    by_url.entry(url).or_default().push(unit);
                }
            }
            if let Some(raw) = string(unit, "raw_path") {
                by_raw.insert(raw, unit);
            }
        }
        let readable = fields(deob, "units")
            .iter()
            .filter_map(|row| {
                Some((
                    string(row, "raw_path")?,
                    string(row, "readable_output_path")?,
                ))
            })
            .collect::<BTreeMap<_, _>>();
        let references = fields(references, "code_units")
            .iter()
            .filter_map(|unit| Some((string(unit, "raw_path")?, fields(unit, "references"))))
            .collect::<BTreeMap<_, _>>();
        Self {
            js_units,
            by_raw,
            by_url,
            references,
            readable,
        }
    }

    fn append_declared(
        &self,
        manifest: &Value,
        lines: &mut Vec<String>,
        global_seen: &mut BTreeSet<&'a str>,
        budget: &WorkBudget,
    ) -> Result<usize> {
        let documents = fields(manifest, "resources")
            .iter()
            .filter_map(|row| Some((row.get("id")?.as_u64()?, string(row, "url")?)))
            .collect::<BTreeMap<_, _>>();
        let mut roots = 0;
        for script in fields(manifest, "inline_scripts") {
            budget.consume(1)?;
            if !is_executable_script(string(script, "script_type")) {
                continue;
            }
            roots += 1;
            let document = script
                .get("parent_resource_id")
                .and_then(Value::as_u64)
                .and_then(|id| documents.get(&id).copied())
                .unwrap_or("unknown document");
            let ordinal = script.get("ordinal").and_then(Value::as_u64).unwrap_or(0);
            lines.push(format!("## {} — script {ordinal}", code_span(document)));
            lines.push(String::new());
            let inline_root =
                string(script, "output_path").and_then(|raw| self.by_raw.get(raw).copied());
            let roots_for_script =
                string(script, "resolved_src").map_or(inline_root.as_slice(), |src| {
                    lines.push(format!("HTML `src`: {}", code_span(src)));
                    self.by_url.get(src).map_or_default(Vec::as_slice)
                });
            if roots_for_script.is_empty() {
                lines.push("Source body not present in this capture.".into());
                lines.push(String::new());
                continue;
            }
            self.append_reachable(
                lines,
                roots_for_script,
                "declared entrypoint",
                global_seen,
                budget,
            )?;
            lines.push(String::new());
        }
        if roots == 0 {
            lines.push("No executable HTML script declarations were found in this capture.".into());
            lines.push(String::new());
        }
        Ok(roots)
    }

    fn append_preloads(
        &self,
        manifest: &Value,
        lines: &mut Vec<String>,
        global_seen: &mut BTreeSet<&'a str>,
        budget: &WorkBudget,
    ) -> Result<()> {
        let mut preloads = Vec::new();
        for document in fields(manifest, "resources") {
            let refs = fields(document, "references");
            budget.consume(u64::try_from(refs.len())?)?;
            preloads.extend(
                refs.iter()
                    .filter(|reference| {
                        matches!(
                            string(reference, "kind"),
                            Some("modulepreload" | "script_preload")
                        )
                    })
                    .map(|reference| (document, reference)),
            );
        }
        if !preloads.is_empty() {
            lines.extend([
                "## HTML script preload hints".into(),
                String::new(),
                "These resources were declared in HTML `<link rel=modulepreload>` or `<link rel=preload as=script>` tags. Preloading is not proof of execution; the listed dependencies are statically discoverable source code.".into(),
                String::new(),
            ]);
            for (document, reference) in preloads {
                let document_url = string(document, "url").unwrap_or("unknown document");
                let kind = string(reference, "kind").unwrap_or("preload");
                let url = string(reference, "resolved_url").unwrap_or_default();
                lines.push(format!(
                    "### {} — {} {}",
                    code_span(document_url),
                    code_span(kind),
                    code_span(url)
                ));
                lines.push(String::new());
                if let Some(units) = self.by_url.get(url) {
                    self.append_reachable(
                        lines,
                        units,
                        &format!("HTML {} hint", code_span(kind)),
                        global_seen,
                        budget,
                    )?;
                } else {
                    lines.push("Preloaded script body not present in this capture.".into());
                }
                lines.push(String::new());
            }
        }
        Ok(())
    }

    fn append_unlinked(&self, lines: &mut Vec<String>, global_seen: &BTreeSet<&str>) {
        let unlinked = self
            .js_units
            .iter()
            .filter(|unit| string(unit, "raw_path").is_some_and(|path| !global_seen.contains(path)))
            .collect::<Vec<_>>();
        if !unlinked.is_empty() {
            lines.extend([
                "## Other captured JavaScript".into(),
                String::new(),
                "These files are not reached from an HTML-declared script through the statically resolved edges above. They may be preloads, workers, runtime-loaded resources or unrelated captured pages.".into(),
                String::new(),
            ]);
            for unit in unlinked {
                lines.push(format!("- {}", path_link(unit, &self.readable)));
            }
            lines.push(String::new());
        }
    }

    fn append_reachable(
        &self,
        lines: &mut Vec<String>,
        roots: &[&'a Value],
        root_reason: &str,
        global_seen: &mut BTreeSet<&'a str>,
        budget: &WorkBudget,
    ) -> Result<()> {
        // Mark at enqueue time: a dense graph must not enqueue one copy of
        // every node for every incoming edge. First BFS reason wins as before.
        let mut queue = VecDeque::new();
        let mut discovered = BTreeSet::<&str>::new();
        budget.consume(u64::try_from(roots.len())?)?;
        for &root in roots {
            if let Some(raw) = string(root, "raw_path") {
                if discovered.insert(raw) {
                    queue.push_back((root, raw, root_reason.to_owned()));
                }
            }
        }
        while let Some((unit, raw, why)) = queue.pop_front() {
            budget.consume(1)?;
            global_seen.insert(raw);
            let source_link = path_link(unit, &self.readable);
            lines.push(format!("- {source_link} — {why}"));
            for reference in self.references.get(raw).copied().unwrap_or_default() {
                budget.consume(1)?;
                let specifier = string(reference, "specifier").unwrap_or("unknown");
                let kind = code_span(string(reference, "kind").unwrap_or("reference"));
                let Some(destination) = string(reference, "resolved_url") else {
                    if !specifier.is_empty() {
                        lines.push(format!("  - {kind} {} — unresolved", code_span(specifier)));
                    }
                    continue;
                };
                let Some(targets) = self.by_url.get(destination) else {
                    lines.push(format!(
                        "  - {kind} {} — not captured ({})",
                        code_span(specifier),
                        code_span(destination)
                    ));
                    continue;
                };
                budget.consume(u64::try_from(targets.len())?)?;
                let mut reason = None;
                for &target in targets {
                    let Some(raw) = string(target, "raw_path") else {
                        continue;
                    };
                    if discovered.insert(raw) {
                        let why = reason.get_or_insert_with(|| {
                            format!("{kind} {} from {source_link}", code_span(specifier))
                        });
                        queue.push_back((target, raw, why.clone()));
                    }
                }
            }
        }
        Ok(())
    }
}

pub struct EntrypointIndex {
    pub(crate) markdown: String,
    pub(crate) declared_scripts: usize,
}

/// Renders a complete navigator of HTML-declared scripts and their
/// statically resolved transitive JavaScript imports. Returns the number of
/// distinct declared script entries; an empty index is still useful for
/// explaining why there is no HTML-root code path in a capture.
pub fn render_entrypoint_index(
    manifest: &Value,
    source_index: &Value,
    deob: &Value,
    references: &Value,
    budget: &WorkBudget,
) -> Result<EntrypointIndex> {
    budget.consume(u64::try_from(fields(source_index, "units").len())?)?;
    budget.consume(u64::try_from(fields(deob, "units").len())?)?;
    budget.consume(u64::try_from(fields(references, "code_units").len())?)?;
    budget.consume(u64::try_from(fields(manifest, "resources").len())?)?;
    let navigation = NavigationIndex::new(source_index, deob, references);
    let mut lines = vec![
        "# JavaScript source entrypoints".to_owned(),
        String::new(),
        "These are the HTML-declared scripts from the captured documents, with the statically resolvable JavaScript import/worker dependencies. This is an index of available source, **not an execution trace**. A missing edge does not mean an import never happened.".into(),
        String::new(),
    ];
    let mut global_seen = BTreeSet::<&str>::new();
    let roots = navigation.append_declared(manifest, &mut lines, &mut global_seen, budget)?;
    navigation.append_preloads(manifest, &mut lines, &mut global_seen, budget)?;
    navigation.append_unlinked(&mut lines, &global_seen);
    budget.checkpoint()?;
    Ok(EntrypointIndex {
        markdown: lines.join("\n"),
        declared_scripts: roots,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    use work_budget::BudgetLimits;

    #[test]
    fn source_links_encode_literal_names_and_stay_project_relative() {
        let unit = json!({"raw_path":"resources/raw.js","source_path":"src/dir/a [b]#?%.js"});
        assert_eq!(
            path_link(&unit, &BTreeMap::new()),
            "[`dir/a [b]#?%.js`](dir/a%20%5Bb%5D%23%3F%25.js)"
        );
        let readable = BTreeMap::from([("resources/raw.js", "//external.example/invalid.js")]);
        assert_eq!(
            path_link(&unit, &readable),
            path_link(&unit, &BTreeMap::new())
        );
        let fallback = json!({"raw_path":"resources/raw.js","source_path":"../invalid.js"});
        assert_eq!(
            path_link(&fallback, &BTreeMap::new()),
            "[`resources/raw.js`](../resources/raw.js)"
        );
        let invalid =
            json!({"raw_path":"C:/outside.js","source_path":"//external.example/script.js"});
        let label = path_link(&invalid, &BTreeMap::new());
        assert!(label.contains("no valid project-local source path"));
        assert!(!label.contains("](//"));
    }

    #[test]
    fn entrypoint_index_escapes_all_labels_and_deduplicates_dense_traversal() -> Result<()> {
        let manifest = json!({
            "resources":[{"id":0,"url":"https://fixture.invalid/[doc]`\n# not a heading"}],
            "inline_scripts":[{"parent_resource_id":0,"ordinal":1,"script_type":"module","resolved_src":"entry"}]
        });
        let units = json!({"units":[
            {"kind":"javascript","raw_path":"resources/a.js","source_path":"src/a.js","url":"entry"},
            {"kind":"javascript","raw_path":"resources/b.js","source_path":"src/b.js","url":"dependency"},
            {"kind":"javascript","raw_path":"resources/c.js","source_path":"src/c.js","url":"dependency"}
        ]});
        let references = json!({"code_units":[
            {"raw_path":"resources/a.js","references":[{"kind":"import_static","specifier":"pkg`\n# fake","resolved_url":"dependency"},{"kind":"import_static","specifier":"second","resolved_url":"dependency"}]},
            {"raw_path":"resources/b.js","references":[{"kind":"import_static","specifier":"cycle","resolved_url":"entry"}]},
            {"raw_path":"resources/c.js","references":[{"kind":"import_static","specifier":"cycle","resolved_url":"entry"}]}
        ]});
        let deob = json!({"units":[]});
        let report = render_entrypoint_index(
            &manifest,
            &units,
            &deob,
            &references,
            &WorkBudget::unlimited("fixture"),
        )?;
        assert_eq!(report.declared_scripts, 1);
        let original = report.markdown;
        assert!(original.contains("`` pkg`\\n# fake ``"), "{original}");
        for body in ["a.js", "b.js", "c.js"] {
            assert_eq!(
                original
                    .lines()
                    .filter(|line| line.starts_with(&format!("- [`{body}`]")))
                    .count(),
                1,
                "{original}"
            );
        }
        assert!(!original.contains("\n# not a heading\n"));
        let budget = WorkBudget::new("exhausted fixture", BudgetLimits::work(12));
        assert!(render_entrypoint_index(&manifest, &units, &deob, &references, &budget).is_err());
        Ok(())
    }
}
