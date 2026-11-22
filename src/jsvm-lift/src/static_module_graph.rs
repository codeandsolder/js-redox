//! Compose initial HTML module roots with the existing contextual JS-reference and
//! import-map resolver output.
//!
//! Never equate raw and transformed source bytes or interpret imported source
//! offsets against the original capture.
use crate::{
    capture_project::CaptureManifest,
    document_entrypoints::{CapturedScriptSource, DocumentEntrypoints},
    sha256_hex,
};
use anyhow::{Context, Result};
use serde::Serialize;
use serde_json::Value;
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fs,
    path::Path,
};
use work_budget::WorkBudget;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ModuleSourceIdentity {
    pub raw_path: String,
    pub raw_sha256: String,
    pub analyzed_path: String,
    pub analyzed_sha256: String,
    pub transform: String,
    pub url: Option<String>,
    pub capture_manifest_resource_ids: Vec<u64>,
    pub capture_manifest_raw_sha256_verified: bool,
}

#[derive(Debug, Clone, Serialize)]
pub struct ModuleRoot {
    pub document_resource_id: u64,
    pub script_ordinal: usize,
    pub source: ModuleSourceIdentity,
}

#[derive(Debug, Clone, Serialize)]
pub struct UnmatchedModuleRoot {
    pub document_resource_id: u64,
    pub script_ordinal: usize,
    pub raw_path: String,
    pub reason: &'static str,
}

#[derive(Debug, Clone, Serialize)]
pub struct ModuleDependency {
    pub document_resource_id: u64,
    pub from: ModuleSourceIdentity,
    /// These are offsets in the transformed/analyzed source, NOT raw JS.
    pub analyzed_source_reference_bytes: [u64; 2],
    pub kind: String,
    pub specifier: String,
    pub resolution: String,
    pub resolved_url: Option<String>,
    pub import_map_key: Option<String>,
    pub import_map_scope: Option<String>,
    pub target_candidates: Vec<ModuleSourceIdentity>,
    pub blocked: bool,
    pub dynamic_import: bool,
}

#[derive(Debug, Clone, Serialize)]
pub struct StaticModuleGraph {
    pub schema: &'static str,
    pub status: &'static str,
    pub roots: Vec<ModuleRoot>,
    pub unmatched_module_roots: Vec<UnmatchedModuleRoot>,
    pub dependencies: Vec<ModuleDependency>,
    pub visited_module_contexts: usize,
    pub unresolved_specifiers: usize,
    pub ambiguous_captured_targets: usize,
    pub raw_and_analyzed_source_hashes_verified: bool,
    pub source_offset_contract: &'static str,
    pub import_map_timing_proven: bool,
}

struct Unit<'a> {
    row: &'a Value,
    raw_path: &'a str,
    analyzed_path: &'a str,
    transform: &'a str,
    origin: &'a str,
}

#[derive(Debug, Clone, Copy)]
struct CapturedManifestBody<'a> {
    sha256: &'a str,
    resource_id: Option<u64>,
    parent_resource_id: Option<u64>,
    ordinal: Option<u64>,
    url: Option<&'a str>,
}
type ManifestBodies<'a> = BTreeMap<(&'a str, &'a str), Vec<CapturedManifestBody<'a>>>;

fn manifest_bodies(manifest: &CaptureManifest) -> ManifestBodies<'_> {
    let mut out = ManifestBodies::new();
    for (origin, rows) in [
        ("resource", &manifest.resources),
        ("inline_script", &manifest.inline_scripts),
    ] {
        for row in rows {
            if let (Some(raw), Some(sha)) = (field(row, "output_path"), field(row, "sha256")) {
                out.entry((raw, origin))
                    .or_default()
                    .push(CapturedManifestBody {
                        sha256: sha,
                        resource_id: row.get("id").and_then(Value::as_u64),
                        parent_resource_id: row.get("parent_resource_id").and_then(Value::as_u64),
                        ordinal: row.get("ordinal").and_then(Value::as_u64),
                        url: field(row, "url"),
                    });
            }
        }
    }
    out
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct SourceIndexLink<'a> {
    transform: &'a str,
    origin: &'a str,
    kind: &'a str,
}

fn field<'a>(value: &'a Value, key: &str) -> Option<&'a str> {
    value.get(key).and_then(Value::as_str)
}

fn source_identity(
    project: &Path,
    unit: &Unit<'_>,
    bodies: &ManifestBodies<'_>,
    budget: &WorkBudget,
) -> Result<ModuleSourceIdentity> {
    budget.consume(1)?;
    let raw = fs::read(project.join(unit.raw_path))
        .with_context(|| format!("reading original source {}", unit.raw_path))?;
    let analyzed = fs::read(project.join(unit.analyzed_path))
        .with_context(|| format!("reading analyzed source {}", unit.analyzed_path))?;
    let raw_sha = sha256_hex(&raw);
    let analyzed_sha = sha256_hex(&analyzed);
    let captured = bodies
        .get(&(unit.raw_path, unit.origin))
        .filter(|rows| !rows.is_empty())
        .with_context(|| {
            format!(
                "module source has no original capture manifest identity: {} ({})",
                unit.raw_path, unit.origin
            )
        })?;
    let mut resource_ids = Vec::new();
    let mut matched_identity = false;
    let row_resource_id = unit.row.get("resource_id").and_then(Value::as_u64);
    let row_ordinal = unit.row.get("ordinal").and_then(Value::as_u64);
    let row_url = field(unit.row, "url");
    for body in captured {
        // Different manifest entries can intentionally refer to identical
        // captured bytes; all must agree on the physical raw digest.
        anyhow::ensure!(
            body.sha256 == raw_sha,
            "captured source differs from manifest SHA: {} ({})",
            unit.raw_path,
            unit.origin
        );
        let matches = match unit.origin {
            "resource" => {
                row_resource_id.is_some()
                    && body.resource_id == row_resource_id
                    && body.url == row_url
            }
            "inline_script" => {
                row_resource_id.is_some()
                    && row_ordinal.is_some()
                    && body.parent_resource_id == row_resource_id
                    && body.ordinal == row_ordinal
            }
            _ => false,
        };
        if matches {
            matched_identity = true;
            if let Some(id) = body.resource_id {
                resource_ids.push(id);
            }
        }
    }
    anyhow::ensure!(
        matched_identity,
        "indexed module has no matching exact capture identity: {} ({})",
        unit.raw_path,
        unit.origin
    );
    resource_ids.sort_unstable();
    resource_ids.dedup();
    anyhow::ensure!(
        field(unit.row, "content_sha256") == Some(analyzed_sha.as_str()),
        "analysis source digest mismatch: {}",
        unit.analyzed_path
    );
    Ok(ModuleSourceIdentity {
        raw_path: unit.raw_path.to_string(),
        raw_sha256: raw_sha,
        analyzed_path: unit.analyzed_path.to_string(),
        analyzed_sha256: analyzed_sha,
        transform: unit.transform.to_string(),
        url: field(unit.row, "url").map(str::to_owned),
        capture_manifest_resource_ids: resource_ids,
        capture_manifest_raw_sha256_verified: true,
    })
}

fn candidate_resolutions(reference: &Value, document_id: u64) -> Vec<&Value> {
    // A present contextual inventory is authoritative. Empty or malformed
    // arrays do not license falling back to potentially stale summary fields.
    // The summary fallback remains for legacy records without this field.
    match reference.get("resolution_candidates") {
        None => vec![reference],
        Some(Value::Array(choices)) => choices
            .iter()
            .filter(|candidate| {
                candidate
                    .get("document_resource_id")
                    .and_then(Value::as_u64)
                    == Some(document_id)
            })
            .collect(),
        Some(_) => Vec::new(),
    }
}

struct RootCapture<'a> {
    source: &'a CapturedScriptSource,
    document_id: u64,
    ordinal: usize,
}

fn match_root(
    root: &RootCapture<'_>,
    raw_index: &BTreeMap<String, Vec<usize>>,
    units: &[Unit<'_>],
    bodies: &ManifestBodies<'_>,
    project: &Path,
    budget: &WorkBudget,
) -> Result<Vec<(usize, ModuleSourceIdentity)>> {
    let mut out = Vec::new();
    for &idx in raw_index
        .get(&root.source.output_path)
        .into_iter()
        .flatten()
    {
        let unit = &units[idx];
        let row_id = unit.row.get("resource_id").and_then(Value::as_u64);
        let matched = root.source.resource_id.map_or_else(
            || {
                unit.origin == "inline_script"
                    && row_id == Some(root.document_id)
                    && unit.row.get("ordinal").and_then(Value::as_u64)
                        == u64::try_from(root.ordinal).ok()
            },
            |resource_id| unit.origin == "resource" && row_id == Some(resource_id),
        );
        if !matched {
            continue;
        }
        let identity = source_identity(project, unit, bodies, budget)?;
        anyhow::ensure!(
            identity.raw_sha256 == root.source.sha256 && root.source.matches_manifest_sha256,
            "raw HTML root digest changed: {}",
            root.source.output_path
        );
        out.push((idx, identity));
    }
    Ok(out)
}

struct SourceCatalog<'a> {
    units: Vec<Unit<'a>>,
    raw_index: BTreeMap<String, Vec<usize>>,
    url_index: BTreeMap<String, Vec<usize>>,
}

impl<'a> SourceCatalog<'a> {
    fn build(
        source_rows: &'a [Value],
        reference_rows: &'a [Value],
        budget: &WorkBudget,
    ) -> Result<Self> {
        let mut source_by_path = BTreeMap::<(&str, &str), Option<SourceIndexLink<'_>>>::new();
        for row in source_rows {
            budget.consume(1)?;
            let (Some(raw), Some(analyzed), Some(transform), Some(origin), Some(kind)) = (
                field(row, "raw_path"),
                field(row, "source_path"),
                field(row, "transform"),
                field(row, "origin"),
                field(row, "kind"),
            ) else {
                continue;
            };
            let link = SourceIndexLink {
                transform,
                origin,
                kind,
            };
            source_by_path
                .entry((raw, analyzed))
                .and_modify(|current| {
                    if *current != Some(link) {
                        *current = None;
                    }
                })
                .or_insert(Some(link));
        }
        let mut units = Vec::new();
        let mut raw_index = BTreeMap::<String, Vec<usize>>::new();
        let mut url_index = BTreeMap::<String, Vec<usize>>::new();
        for row in reference_rows {
            budget.consume(1)?;
            let (Some(raw_path), Some(analyzed_path)) =
                (field(row, "raw_path"), field(row, "source_path"))
            else {
                continue;
            };
            let Some(link) = source_by_path
                .get(&(raw_path, analyzed_path))
                .copied()
                .flatten()
            else {
                // Missing or ambiguous raw→formatted provenance: do not connect.
                continue;
            };
            let idx = units.len();
            units.push(Unit {
                row,
                raw_path,
                analyzed_path,
                transform: link.transform,
                origin: link.origin,
            });
            raw_index.entry(raw_path.to_string()).or_default().push(idx);
            // A document URL is also the URL of every inline script within it.
            // Imported modules cannot resolve to arbitrary inline script bodies
            // just because they share that document URL.
            if link.kind == "javascript" && link.origin == "resource" {
                if let Some(url) = field(row, "url").filter(|url| !url.is_empty()) {
                    url_index.entry(url.to_owned()).or_default().push(idx);
                }
            }
        }
        Ok(Self {
            units,
            raw_index,
            url_index,
        })
    }
}

struct RootDiscovery {
    roots: Vec<ModuleRoot>,
    unmatched_module_roots: Vec<UnmatchedModuleRoot>,
    identities: BTreeMap<usize, ModuleSourceIdentity>,
    queue: VecDeque<(u64, usize)>,
}

fn discover_roots(
    project: &Path,
    documents: &[DocumentEntrypoints],
    catalog: &SourceCatalog<'_>,
    bodies: &ManifestBodies<'_>,
    budget: &WorkBudget,
) -> Result<RootDiscovery> {
    let mut roots = Vec::new();
    let mut unmatched_module_roots = Vec::new();
    let mut identities = BTreeMap::<usize, ModuleSourceIdentity>::new();
    let mut queue = VecDeque::<(u64, usize)>::new();
    for document in documents {
        for script in &document.scripts {
            budget.consume(1)?;
            if !script.executable || !script.is_module {
                continue;
            }
            for source in &script.captured_sources {
                let resolved = match_root(
                    &RootCapture {
                        source,
                        document_id: document.document_resource_id,
                        ordinal: script.ordinal,
                    },
                    &catalog.raw_index,
                    &catalog.units,
                    bodies,
                    project,
                    budget,
                )?;
                if resolved.is_empty() {
                    unmatched_module_roots.push(UnmatchedModuleRoot {
                        document_resource_id: document.document_resource_id,
                        script_ordinal: script.ordinal,
                        raw_path: source.output_path.clone(),
                        reason: "captured_source_not_indexed_in_js_references_or_source_index",
                    });
                }
                for (idx, identity) in resolved {
                    identities.insert(idx, identity.clone());
                    roots.push(ModuleRoot {
                        document_resource_id: document.document_resource_id,
                        script_ordinal: script.ordinal,
                        source: identity,
                    });
                    queue.push_back((document.document_resource_id, idx));
                }
            }
        }
    }
    Ok(RootDiscovery {
        roots,
        unmatched_module_roots,
        identities,
        queue,
    })
}

struct GraphTraversal<'a, 'source, 'manifest> {
    project: &'a Path,
    budget: &'a WorkBudget,
    catalog: &'a SourceCatalog<'source>,
    bodies: &'a ManifestBodies<'manifest>,
    identities: BTreeMap<usize, ModuleSourceIdentity>,
    queue: VecDeque<(u64, usize)>,
    visited: BTreeSet<(u64, usize)>,
    dependencies: Vec<ModuleDependency>,
    unresolved: usize,
    ambiguous: usize,
}

impl<'a, 'source, 'manifest> GraphTraversal<'a, 'source, 'manifest> {
    const fn new(
        project: &'a Path,
        budget: &'a WorkBudget,
        catalog: &'a SourceCatalog<'source>,
        bodies: &'a ManifestBodies<'manifest>,
        identities: BTreeMap<usize, ModuleSourceIdentity>,
        queue: VecDeque<(u64, usize)>,
    ) -> Self {
        Self {
            project,
            budget,
            catalog,
            bodies,
            identities,
            queue,
            visited: BTreeSet::new(),
            dependencies: Vec::new(),
            unresolved: 0,
            ambiguous: 0,
        }
    }

    fn identity(&mut self, idx: usize) -> Result<ModuleSourceIdentity> {
        if let Some(existing) = self.identities.get(&idx) {
            return Ok(existing.clone());
        }
        let identity = source_identity(
            self.project,
            &self.catalog.units[idx],
            self.bodies,
            self.budget,
        )?;
        self.identities.insert(idx, identity.clone());
        Ok(identity)
    }

    fn traverse(&mut self) -> Result<()> {
        while let Some((document_id, idx)) = self.queue.pop_front() {
            self.budget.consume(1)?;
            if !self.visited.insert((document_id, idx)) {
                continue;
            }
            let from = self.identity(idx)?;
            let catalog = self.catalog;
            let Some(references) = catalog.units[idx]
                .row
                .get("references")
                .and_then(Value::as_array)
            else {
                continue;
            };
            for reference in references {
                self.visit_reference(document_id, &from, reference)?;
            }
        }
        Ok(())
    }

    // The contextual inventory is authoritative, including zero candidates.
    // Dynamic edges remain visible without entering the traversal queue.
    fn visit_reference(
        &mut self,
        document_id: u64,
        from: &ModuleSourceIdentity,
        reference: &Value,
    ) -> Result<()> {
        self.budget.consume(1)?;
        let Some(kind) = field(reference, "kind") else {
            return Ok(());
        };
        let is_static = matches!(kind, "import_static" | "reexport_named" | "reexport_all");
        let dynamic = kind == "import_dynamic";
        if !(is_static || dynamic) {
            return Ok(());
        }
        let specifier = field(reference, "specifier").unwrap_or_default();
        let span = [
            reference.get("start").and_then(Value::as_u64).unwrap_or(0),
            reference.get("end").and_then(Value::as_u64).unwrap_or(0),
        ];
        let choices = candidate_resolutions(reference, document_id);
        if choices.is_empty() {
            self.unresolved += 1;
            self.dependencies.push(ModuleDependency {
                document_resource_id: document_id,
                from: from.clone(),
                analyzed_source_reference_bytes: span,
                kind: kind.to_string(),
                specifier: specifier.to_owned(),
                resolution: "no_matching_document_resolution".into(),
                resolved_url: None,
                import_map_key: None,
                import_map_scope: None,
                target_candidates: Vec::new(),
                blocked: false,
                dynamic_import: dynamic,
            });
        }
        for choice in choices {
            self.budget.consume(1)?;
            let resolved_url = field(choice, "resolved_url").map(str::to_owned);
            let resolution = field(choice, "resolution").unwrap_or("unknown").to_owned();
            let blocked = resolution == "import_map_blocked";
            let mut target_candidates = Vec::new();
            if let Some(url) = resolved_url.as_ref().filter(|_| !blocked) {
                for &target in self.catalog.url_index.get(url).into_iter().flatten() {
                    self.budget.consume(1)?;
                    let target_identity = self.identity(target)?;
                    target_candidates.push(target_identity);
                    if is_static {
                        self.queue.push_back((document_id, target));
                    }
                }
            }
            if resolved_url.is_none() || target_candidates.is_empty() {
                self.unresolved += 1;
            }
            if target_candidates.len() > 1 {
                self.ambiguous += 1;
            }
            self.dependencies.push(ModuleDependency {
                document_resource_id: document_id,
                from: from.clone(),
                analyzed_source_reference_bytes: span,
                kind: kind.to_string(),
                specifier: specifier.to_owned(),
                resolution,
                resolved_url,
                import_map_key: field(choice, "import_map_key").map(str::to_owned),
                import_map_scope: field(choice, "scope").map(str::to_owned),
                target_candidates,
                blocked,
                dynamic_import: dynamic,
            });
        }
        Ok(())
    }
}

/// Traverse only imports/re-exports that are statically named by a module.
///
/// The caller supplies the EXISTING project-js-refs stage's contextual
/// `resolution_candidates`, which already incorporates captured import maps.
/// Dynamic imports are retained as candidate edges but not followed.
/// Missing modules are explicit, and same-URL different capture responses
/// remain distinct alternatives. All source bytes are rehashed on use.
///
/// # Errors
///
/// Fails if the source index or reference inventory lacks its required arrays, or if the work
/// budget is exhausted. Source decoding and linking failures from delegated helpers also
/// propagate.
pub fn link_static_modules(
    project: &Path,
    documents: &[DocumentEntrypoints],
    source_index: &Value,
    js_references: &Value,
    manifest: &CaptureManifest,
    budget: &WorkBudget,
) -> Result<StaticModuleGraph> {
    let bodies = manifest_bodies(manifest);
    let source_rows = source_index
        .get("units")
        .and_then(Value::as_array)
        .context("source index has no units")?;
    let reference_rows = js_references
        .get("code_units")
        .and_then(Value::as_array)
        .context("JS references have no code_units")?;
    let catalog = SourceCatalog::build(source_rows, reference_rows, budget)?;
    let RootDiscovery {
        mut roots,
        unmatched_module_roots,
        identities,
        queue,
    } = discover_roots(project, documents, &catalog, &bodies, budget)?;
    let mut traversal = GraphTraversal::new(project, budget, &catalog, &bodies, identities, queue);
    traversal.traverse()?;
    let GraphTraversal {
        mut dependencies,
        visited,
        unresolved,
        ambiguous,
        ..
    } = traversal;
    roots.sort_by(|a, b| {
        (a.document_resource_id, a.script_ordinal, &a.source.raw_path).cmp(&(
            b.document_resource_id,
            b.script_ordinal,
            &b.source.raw_path,
        ))
    });
    dependencies.sort_by(|a, b| {
        (
            a.document_resource_id,
            &a.from.raw_path,
            a.analyzed_source_reference_bytes,
            &a.specifier,
        )
            .cmp(&(
                b.document_resource_id,
                &b.from.raw_path,
                b.analyzed_source_reference_bytes,
                &b.specifier,
            ))
    });
    Ok(StaticModuleGraph {
        schema: "jsvm-static-module-graph/v1",
        status: "analyzed",
        roots,
        unmatched_module_roots,
        dependencies,
        visited_module_contexts: visited.len(),
        unresolved_specifiers: unresolved,
        ambiguous_captured_targets: ambiguous,
        raw_and_analyzed_source_hashes_verified: true,
        source_offset_contract: "Import reference byte spans are relative to analyzed_path + analyzed_sha256 only; raw_sha256 corresponds to original source and has no automatically inferred offset mapping",
        import_map_timing_proven: false,
    })
}

#[cfg(test)]
mod tests {
    use super::link_static_modules;
    use crate::{
        capture_project::{CaptureManifest, CaptureSource},
        document_entrypoints::{
            CapturedScriptSource, DocumentEntrypoints, DocumentScriptRoot, ScriptAttributes,
        },
        sha256_hex,
    };
    use serde_json::json;
    use std::{fs, path::Path};
    use work_budget::WorkBudget;

    #[test]
    fn contextual_resolution_field_must_be_well_formed_and_document_specific() {
        let stale = "https://example.test/pkg.js";
        let empty = json!({"resolution_candidates":[],"resolved_url":stale});
        assert_eq!(super::candidate_resolutions(&empty, 3).len(), 0);
        let malformed = json!({"resolution_candidates":"invalid","resolved_url":stale});
        assert_eq!(super::candidate_resolutions(&malformed, 3).len(), 0);
        let mismatched = json!({"resolution_candidates":[
            {"document_resource_id":4,"resolved_url":stale}
        ],"resolved_url":stale});
        assert_eq!(super::candidate_resolutions(&mismatched, 3).len(), 0);
        assert_eq!(super::candidate_resolutions(&mismatched, 4).len(), 1);
        let legacy = json!({"resolved_url":stale});
        assert_eq!(super::candidate_resolutions(&legacy, 3).len(), 1);
    }

    fn pair(
        project: &Path,
        name: &str,
        original: &str,
        transformed: &str,
    ) -> anyhow::Result<(serde_json::Value, serde_json::Value, String)> {
        let raw_path = format!("resources/{name}.js");
        let source_path = format!("src/{name}.js");
        fs::write(project.join(&raw_path), original)?;
        fs::write(project.join(&source_path), transformed)?;
        let source_index_row = json!({
            "raw_path":raw_path,
            "source_path":source_path,
            "transform":"prettified",
            "origin":"resource",
            "kind":"javascript"
        });
        let refs_row = json!({
            "raw_path":raw_path,
            "source_path":source_path,
            "content_sha256":sha256_hex(transformed.as_bytes()),
            "url":format!("https://example.test/{name}.js"),
            "references":[]
        });
        Ok((source_index_row, refs_row, sha256_hex(original.as_bytes())))
    }

    #[test]
    fn contextual_static_imports_follow_transformed_sources_not_original_offsets(
    ) -> anyhow::Result<()> {
        let root = tempfile::tempdir()?;
        let project = root.path();
        fs::create_dir(project.join("resources"))?;
        fs::create_dir(project.join("src"))?;
        let (main_unit, main_refs, main_sha) = pair(
            project,
            "main",
            "import 'pkg';import('./lazy.js');import 'ghost';import 'blocked';",
            "import 'pkg';\nimport('./lazy.js');\nimport 'ghost';\nimport 'blocked';\n",
        )?;
        let (first_unit, mut first_refs, _) = pair(
            project,
            "pkg-v1",
            "export*from './dep.js'",
            "export * from './dep.js';\n",
        )?;
        let (second_unit, second_refs, _) = pair(
            project,
            "pkg-v2",
            "export const version=2",
            "export const version = 2;\n",
        )?;
        let (dep_unit, dep_refs, _) =
            pair(project, "dep", "export const d=1", "export const d = 1;\n")?;
        let (lazy_unit, lazy_refs, _) = pair(
            project,
            "lazy",
            "export const lazy=1",
            "export const lazy = 1;\n",
        )?;
        // An inline JS body sharing an import URL is not a fetched module.
        let (mut inline_unit, mut inline_refs, _) =
            pair(project, "fake-inline", "const fake=1", "const fake = 1;\n")?;
        inline_unit["origin"] = json!("inline_script");
        inline_refs["url"] = json!("https://example.test/pkg.js");

        let mut main_refs = main_refs;
        main_refs["references"] = json!([
            {
                "kind":"import_static", "specifier":"pkg", "start":0,"end":13,
                "resolution_candidates":[
                    {
                        "document_resource_id":3,
                        "resolution":"import_map",
                        "resolved_url":"https://example.test/pkg.js",
                        "import_map_key":"pkg",
                        "scope":null
                    }
                ]
            },
            {
                "kind":"import_dynamic", "specifier":"./lazy.js","start":14,"end":33,
                "resolution":"url","resolved_url":"https://example.test/lazy.js"
            },
            {
                "kind":"import_static", "specifier":"ghost", "start":35, "end":50,
                "resolution_candidates":[],
                "resolution":"url","resolved_url":"https://example.test/pkg.js"
            },
            {
                "kind":"import_static", "specifier":"blocked", "start":51, "end":68,
                "resolution_candidates":[{
                    "document_resource_id":3,"resolution":"import_map_blocked",
                    "resolved_url":"https://example.test/pkg.js"
                }]
            }
        ]);
        main_refs["url"] = json!("https://example.test/main.js");
        first_refs["url"] = json!("https://example.test/pkg.js");
        first_refs["references"] = json!([{
            "kind":"reexport_all","specifier":"./dep.js","start":0,"end":25,
            "resolution":"url","resolved_url":"https://example.test/dep.js"
        }]);
        let mut second_refs = second_refs;
        second_refs["url"] = json!("https://example.test/pkg.js");
        let mut index =
            json!({"units":[main_unit,first_unit,second_unit,dep_unit,lazy_unit,inline_unit]});
        let mut refs =
            json!({"code_units":[main_refs,first_refs,second_refs,dep_refs,lazy_refs,inline_refs]});
        for i in 0..5 {
            index["units"][i]["resource_id"] = json!(i);
            refs["code_units"][i]["resource_id"] = json!(i);
        }
        index["units"][5]["resource_id"] = json!(3);
        index["units"][5]["ordinal"] = json!(99);
        refs["code_units"][5]["resource_id"] = json!(3);
        refs["code_units"][5]["ordinal"] = json!(99);
        let mut resources = Vec::new();
        let mut inline_scripts = Vec::new();
        for (i, unit) in index["units"].as_array().into_iter().flatten().enumerate() {
            let raw_path = unit["raw_path"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("fixture source raw path"))?;
            let sha = sha256_hex(&fs::read(project.join(raw_path))?);
            let url = refs["code_units"][i]["url"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("fixture source URL"))?;
            if unit["origin"] == "inline_script" {
                inline_scripts.push(json!({
                    "output_path":raw_path,"sha256":sha,
                    "parent_resource_id":3,"ordinal":99
                }));
            } else {
                resources.push(json!({
                    "output_path":raw_path,"sha256":sha,
                    "id":i,"url":url,"kind":"javascript"
                }));
            }
        }
        let manifest = CaptureManifest {
            schema: "capture-project/v1".into(),
            source: CaptureSource {
                kind: "test".into(),
                input: "synthetic".into(),
                salvaged: false,
                extra: serde_json::Map::new(),
            },
            pages: vec![],
            resources,
            inline_scripts,
            counts: std::collections::BTreeMap::new(),
            extra: serde_json::Map::new(),
        };
        let source = CapturedScriptSource {
            resource_id: Some(0),
            output_path: "resources/main.js".into(),
            sha256: main_sha,
            matches_manifest_sha256: true,
        };
        let make_document = |document_resource_id| DocumentEntrypoints {
            document_resource_id,
            document_url: "https://example.test/".into(),
            document_source_sha256: "unused".into(),
            document_matches_manifest_sha256: true,
            static_base_url: "https://example.test/".into(),
            scripts: vec![DocumentScriptRoot {
                ordinal: 1,
                script_type: "module".into(),
                executable: true,
                is_module: true,
                attributes: ScriptAttributes::default(),
                scheduling_class: "deferred",
                src: Some("main.js".into()),
                resolved_url: Some("https://example.test/main.js".into()),
                captured_sources: vec![source.clone()],
                execution_observed: false,
            }],
        };
        let budget = WorkBudget::unlimited("static-module-graph-test");
        let result = link_static_modules(
            project,
            &[make_document(3), make_document(4)],
            &index,
            &refs,
            &manifest,
            &budget,
        )?;
        assert_eq!(result.roots.len(), 2);
        assert!(result.unmatched_module_roots.is_empty());
        let root_source = &result.roots[0].source;
        assert_ne!(root_source.raw_sha256, root_source.analyzed_sha256);
        assert_eq!(root_source.transform, "prettified");
        assert!(root_source.capture_manifest_raw_sha256_verified);
        assert_eq!(root_source.capture_manifest_resource_ids, vec![0]);
        assert!(result
            .dependencies
            .iter()
            .flat_map(|edge| &edge.target_candidates)
            .all(|body| body.capture_manifest_raw_sha256_verified));
        assert_eq!(result.visited_module_contexts, 5);
        // An explicit empty per-document inventory overrides stale summary
        // resolution fields, even if their URL is otherwise a captured module.
        for document_id in [3, 4] {
            let ghost = result
                .dependencies
                .iter()
                .filter(|edge| {
                    edge.document_resource_id == document_id && edge.specifier == "ghost"
                })
                .collect::<Vec<_>>();
            assert_eq!(ghost.len(), 1);
            assert_eq!(ghost[0].resolution, "no_matching_document_resolution");
            assert_eq!(ghost[0].resolved_url, None);
            assert_eq!(ghost[0].target_candidates.len(), 0);
            assert!(!ghost[0].blocked);
        }
        assert_eq!(result.unresolved_specifiers, 5);
        for document_id in [3, 4] {
            let blocked = result
                .dependencies
                .iter()
                .filter(|edge| {
                    edge.document_resource_id == document_id && edge.specifier == "blocked"
                })
                .collect::<Vec<_>>();
            assert_eq!(blocked.len(), 1);
            assert_eq!(blocked[0].target_candidates.len(), 0);
            if document_id == 3 {
                assert!(blocked[0].blocked);
                assert_eq!(blocked[0].resolution, "import_map_blocked");
            } else {
                assert_eq!(blocked[0].resolution, "no_matching_document_resolution");
            }
        } // doc3: root, both pkg versions, dep; doc4: root; dynamic lazy is not traversed.
        assert!(result
            .dependencies
            .iter()
            .any(|edge| edge.document_resource_id == 3
                && edge.kind == "import_static"
                && edge.target_candidates.len() == 2
                && edge.import_map_key.as_deref() == Some("pkg")
                && edge.analyzed_source_reference_bytes == [0, 13]));
        assert!(result
            .dependencies
            .iter()
            .any(|edge| edge.document_resource_id == 4
                && edge.resolution == "no_matching_document_resolution"
                && edge.target_candidates.is_empty()));
        assert!(result
            .dependencies
            .iter()
            .any(|edge| edge.document_resource_id == 3
                && edge.kind == "reexport_all"
                && edge.target_candidates.len() == 1));
        assert!(result
            .dependencies
            .iter()
            .any(|edge| edge.document_resource_id == 3
                && edge.dynamic_import
                && edge.resolved_url.as_deref() == Some("https://example.test/lazy.js")
                && edge.target_candidates.len() == 1));
        assert!(!result
            .roots
            .iter()
            .any(|root| root.source.raw_path.contains("lazy")));
        assert_eq!(result.ambiguous_captured_targets, 1);
        assert!(!result.import_map_timing_proven);
        let mut tampered = make_document(3);
        tampered.scripts[0].captured_sources[0].sha256 = "tampered".into();
        assert!(
            link_static_modules(project, &[tampered], &index, &refs, &manifest, &budget).is_err()
        );
        let mut changed_manifest = manifest;
        changed_manifest.resources[1]["sha256"] = json!("incorrect-target-hash");
        assert!(link_static_modules(
            project,
            &[make_document(3)],
            &index,
            &refs,
            &changed_manifest,
            &budget
        )
        .is_err());
        Ok(())
    }
}
