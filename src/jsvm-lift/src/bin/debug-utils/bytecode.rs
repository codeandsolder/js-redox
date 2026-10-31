use anyhow::{bail, Context, Result};
use jsvm_lift::parse_int::{parse_int_aliases, resolve_literal_parse_int};
use serde_json::{json, Value};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    process::Command,
};

fn concatenated_json(path: &Path) -> Result<Vec<Value>> {
    let text = fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;
    let mut out = Vec::new();
    for item in serde_json::Deserializer::from_str(&text).into_iter::<Value>() {
        match item {
            Ok(value) => out.push(value),
            Err(error) => {
                eprintln!(
                    "[warning] trailing/incomplete JSON ignored in {}: {error}",
                    path.display()
                );
                break;
            }
        }
    }
    Ok(out)
}

fn usize_field(value: Option<&Value>, label: &str) -> Result<usize> {
    let raw = value
        .and_then(Value::as_u64)
        .with_context(|| format!("{label} must be a non-negative integer"))?;
    usize::try_from(raw).with_context(|| format!("{label} does not fit usize"))
}

fn u64_field(value: Option<&Value>, label: &str) -> Result<u64> {
    value
        .and_then(Value::as_u64)
        .with_context(|| format!("{label} must be a non-negative integer"))
}

fn selector_domain(masks: impl IntoIterator<Item = u64>) -> Option<BTreeSet<u64>> {
    let masks = masks.into_iter().collect::<BTreeSet<_>>();
    if masks.is_empty() || masks.iter().any(|mask| !mask.is_power_of_two()) {
        return None;
    }
    let combined = masks.iter().fold(0_u64, |acc, mask| acc | mask);
    let bits = u32::try_from(masks.len()).ok()?;
    // This is a diagnostic domain expansion, not a reason to allocate an
    // attacker-sized set from arbitrary scanner JSON.
    if bits > 20 {
        return None;
    }
    let expected = 1_u64.checked_shl(bits)?;
    if combined.checked_add(1)? != expected {
        return None;
    }
    Some((0..expected).collect())
}

fn unknown_map(builder: &Value) -> Result<BTreeMap<usize, String>> {
    let mut out = BTreeMap::new();
    for unknown in builder
        .get("unknowns")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
    {
        let index = usize_field(unknown.get("index"), "unknown index")?;
        let preview = unknown
            .get("preview")
            .and_then(Value::as_str)
            .unwrap_or_default()
            .to_owned();
        out.insert(index, preview);
    }
    Ok(out)
}

fn values(builder: &Value) -> Result<&[Value]> {
    builder
        .get("values")
        .and_then(Value::as_array)
        .map(Vec::as_slice)
        .context("builder values must be an array")
}

fn resolved_value(value: &Value, expr: Option<&str>, aliases: &BTreeSet<String>) -> Option<u64> {
    value
        .as_u64()
        .or_else(|| expr.and_then(|text| resolve_literal_parse_int(text, aliases)))
}

fn format_field(value: &Value, expr: Option<&str>, aliases: &BTreeSet<String>) -> String {
    if let Some(raw) = value.as_u64() {
        return raw.to_string();
    }
    if let Some(text) = expr {
        if let Some(resolved) = resolve_literal_parse_int(text, aliases) {
            return format!("{resolved}{{{text}}}");
        }
        return format!("{{{text}}}");
    }
    "{?}".to_owned()
}

pub fn dump_linked_bytecode(
    jsonl: &Path,
    instructions: usize,
    max_decoders: Option<usize>,
    builder_start: Option<u64>,
    include_all: bool,
) -> Result<()> {
    for report in concatenated_json(jsonl)? {
        let mut builders = BTreeMap::<u64, &Value>::new();
        for builder in report
            .get("push_builders")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
        {
            builders.insert(u64_field(builder.get("start"), "builder start")?, builder);
        }

        let source_path = report
            .get("file")
            .and_then(Value::as_str)
            .map(PathBuf::from)
            .context("scan report missing file")?;
        let source = fs::read_to_string(&source_path).unwrap_or_default();
        let aliases = parse_int_aliases(&source);
        let name = source_path
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("<unknown>");
        println!("\n== {name} ==");
        if !aliases.is_empty() {
            println!(
                "parseInt aliases: {}",
                aliases.iter().cloned().collect::<Vec<_>>().join(", ")
            );
        }

        let mut shown = 0_usize;
        let mut report_observed = BTreeSet::new();
        let mut report_selector_domain = BTreeSet::new();
        for decoder in report
            .get("decoder_candidates")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
        {
            let decoder_builder_start = decoder.get("builder_start").and_then(Value::as_u64);
            let linked = decoder
                .get("builder_var")
                .is_some_and(|value| !value.is_null())
                && decoder_builder_start.is_some();
            if !linked && !include_all {
                continue;
            }
            if builder_start.is_some() && builder_start != decoder_builder_start {
                continue;
            }
            if max_decoders.is_some_and(|limit| shown >= limit) {
                break;
            }

            let builder = decoder_builder_start.and_then(|start| builders.get(&start).copied());
            let width = u64_field(decoder.get("width"), "decoder width")?;
            let mut canonical_width = None;
            let mut width_score = None;
            let mut candidate_top_scoring = false;
            if let Some(builder) = builder {
                if let Some(hints) = builder.get("width_hints").and_then(Value::as_array) {
                    let top_score = hints
                        .iter()
                        .filter_map(|hint| hint.get("score").and_then(Value::as_i64))
                        .max();
                    if let Some(top_score) = top_score {
                        canonical_width = hints
                            .iter()
                            .filter(|hint| {
                                hint.get("score").and_then(Value::as_i64) == Some(top_score)
                            })
                            .filter_map(|hint| hint.get("width").and_then(Value::as_u64))
                            .min();
                        for hint in hints {
                            if hint.get("width").and_then(Value::as_u64) == Some(width) {
                                width_score = hint.get("score").and_then(Value::as_i64);
                                candidate_top_scoring = width_score == Some(top_score);
                                break;
                            }
                        }
                    }
                }
            }

            let mut confidence = 0_u8;
            let mut reasons = Vec::new();
            if linked {
                confidence += 3;
                reasons.push("builder-linked");
            }
            if let Some(builder) = builder {
                let arguments = u64_field(builder.get("arguments"), "builder arguments")?;
                if width != 0 && arguments % width == 0 {
                    confidence += 1;
                    reasons.push("length-aligned");
                }
            }
            if candidate_top_scoring {
                confidence += 3;
                reasons.push("decoder-width-is-top-scoring-period");
            }
            let mut offsets = decoder
                .get("operand_offsets")
                .and_then(Value::as_array)
                .into_iter()
                .flatten()
                .filter_map(Value::as_u64)
                .collect::<Vec<_>>();
            offsets.sort_unstable();
            if offsets.first() == Some(&0) && offsets.len() >= 2 {
                confidence += 1;
                reasons.push("multiple-fetch-offsets");
            }

            println!(
                "decoder {} object={} builder={} width={width} ip={} base={} offsets={offsets:?} confidence={confidence}/8",
                decoder.get("function_id").and_then(Value::as_str).unwrap_or("?"),
                decoder.get("object").and_then(Value::as_str).unwrap_or("?"),
                decoder.get("builder_var").and_then(Value::as_str).unwrap_or("?"),
                decoder.get("ip").and_then(Value::as_str).unwrap_or("?"),
                decoder.get("base").and_then(Value::as_str).unwrap_or("<inline>"),
            );
            println!(
                "  builder_min_top_period={} linked_decoder_width={width} candidate_width_score={} reasons={}",
                canonical_width.map_or_else(|| "?".to_owned(), |value| value.to_string()),
                width_score.map_or_else(|| "?".to_owned(), |value| value.to_string()),
                reasons.join(",")
            );
            let preview = decoder
                .get("preview")
                .and_then(Value::as_str)
                .unwrap_or_default();
            let preview = preview.get(..preview.len().min(220)).unwrap_or(preview);
            println!("  evidence: {preview}");

            let masks = decoder
                .get("selector_masks")
                .and_then(Value::as_array)
                .into_iter()
                .flatten()
                .filter_map(Value::as_u64)
                .collect::<Vec<_>>();
            let domain = selector_domain(masks.iter().copied());
            if decoder
                .get("selector_var")
                .is_some_and(|value| !value.is_null())
                || !masks.is_empty()
            {
                println!(
                    "  selector: var={} masks={masks:?} domain={}",
                    decoder
                        .get("selector_var")
                        .and_then(Value::as_str)
                        .unwrap_or("?"),
                    domain
                        .as_ref()
                        .map(|values| format!("{values:?}"))
                        .unwrap_or_else(|| "?".to_owned())
                );
                if let Some(domain) = &domain {
                    report_selector_domain.extend(domain.iter().copied());
                }
            }

            let Some(builder) = builder else {
                shown += 1;
                continue;
            };
            let values = values(builder)?;
            let unknowns = unknown_map(builder)?;
            let width_usize = usize::try_from(width).context("decoder width does not fit usize")?;
            if width_usize == 0 {
                bail!("decoder width must be non-zero");
            }
            let instruction_count = values.len() / width_usize;
            let mut opcodes = BTreeSet::new();
            let mut unknown_opcode_slots = 0_usize;
            for instruction in 0..instruction_count {
                let index = instruction * width_usize;
                if let Some(value) = resolved_value(
                    &values[index],
                    unknowns.get(&index).map(String::as_str),
                    &aliases,
                ) {
                    opcodes.insert(value);
                } else {
                    unknown_opcode_slots += 1;
                }
            }
            report_observed.extend(opcodes.iter().copied());
            let known = values.iter().filter(|value| !value.is_null()).count();
            println!(
                "  stream: args={} instructions={instruction_count} known={known}/{}",
                values.len(),
                values.len()
            );
            println!("  opcodes: observed={opcodes:?} unknown_slots={unknown_opcode_slots}");
            if let Some(domain) = &domain {
                println!(
                    "  selector-vs-stream: unobserved={:?} out_of_domain={:?}",
                    domain
                        .difference(&opcodes)
                        .copied()
                        .collect::<BTreeSet<_>>(),
                    opcodes.difference(domain).copied().collect::<BTreeSet<_>>()
                );
            }

            for instruction in 0..instruction_count.min(instructions) {
                let pc = instruction * width_usize;
                let fields = (0..width_usize)
                    .map(|offset| {
                        let index = pc + offset;
                        format_field(
                            &values[index],
                            unknowns.get(&index).map(String::as_str),
                            &aliases,
                        )
                    })
                    .collect::<Vec<_>>();
                println!("    {instruction:04} pc={pc:04}: {}", fields.join(" | "));
            }
            shown += 1;
        }

        if shown == 0 {
            println!("(no linked decoder candidates)");
        } else if !report_observed.is_empty() {
            println!("report opcode union: observed={report_observed:?}");
            if !report_selector_domain.is_empty() {
                println!(
                    "report selector union: domain={report_selector_domain:?} unobserved={:?}",
                    report_selector_domain
                        .difference(&report_observed)
                        .copied()
                        .collect::<BTreeSet<_>>()
                );
            }
        }
    }
    Ok(())
}

fn scanner_path(explicit: Option<&Path>) -> Result<PathBuf> {
    if let Some(path) = explicit {
        if path.is_file() {
            return Ok(path.to_path_buf());
        }
        bail!("scanner binary not found: {}", path.display());
    }
    let current = std::env::current_exe().context("locating debug-utils executable")?;
    let sibling = current
        .parent()
        .context("debug-utils executable has no parent directory")?
        .join("jsvm-lift");
    if sibling.is_file() {
        Ok(sibling)
    } else {
        bail!(
            "jsvm-lift scanner not found beside debug-utils at {}; build workspace bins or pass --scanner",
            sibling.display()
        )
    }
}

fn scan(path: &Path, scanner: &Path) -> Result<Value> {
    let output = Command::new(scanner)
        .arg("--json")
        .arg(path)
        .output()
        .with_context(|| format!("running {}", scanner.display()))?;
    if !output.status.success() {
        bail!(
            "{} failed for {}:\n{}",
            scanner.display(),
            path.display(),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    serde_json::from_slice(&output.stdout)
        .with_context(|| format!("parsing scanner output for {}", path.display()))
}

fn symbolic_field(
    values: &[Value],
    unknowns: &BTreeMap<usize, String>,
    index: usize,
    aliases: &BTreeSet<String>,
) -> Value {
    if let Some(value) = values.get(index).and_then(Value::as_u64) {
        return json!({"kind": "literal", "value": value});
    }
    let Some(expr) = unknowns.get(&index) else {
        return json!({"kind": "symbolic", "expr": "<unknown>"});
    };
    if let Some(value) = resolve_literal_parse_int(expr, aliases) {
        json!({
            "kind": "folded",
            "value": value,
            "expr": expr,
            "rule": "parseInt-alias-literal-radix",
            "confidence": "source-backed",
        })
    } else {
        json!({"kind": "symbolic", "expr": expr})
    }
}

pub fn extract_linked_streams(
    file: &Path,
    scanner: Option<&Path>,
    output: Option<&Path>,
    preview: usize,
) -> Result<()> {
    let scanner = scanner_path(scanner)?;
    let report = scan(file, &scanner)?;
    let source = fs::read_to_string(file).with_context(|| format!("reading {}", file.display()))?;
    let aliases = parse_int_aliases(&source);

    let mut builders = BTreeMap::<(u64, u64), &Value>::new();
    for builder in report
        .get("push_builders")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
    {
        builders.insert(
            (
                u64_field(builder.get("start"), "builder start")?,
                u64_field(builder.get("end"), "builder end")?,
            ),
            builder,
        );
    }
    let mut groups = BTreeMap::<(u64, u64), Vec<&Value>>::new();
    for decoder in report
        .get("decoder_candidates")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
    {
        let (Some(start), Some(end)) = (
            decoder.get("builder_start").and_then(Value::as_u64),
            decoder.get("builder_end").and_then(Value::as_u64),
        ) else {
            continue;
        };
        groups.entry((start, end)).or_default().push(decoder);
    }

    let mut streams = Vec::new();
    for (key, decoders) in groups {
        let Some(builder) = builders.get(&key).copied() else {
            continue;
        };
        let mut widths = BTreeMap::<u64, usize>::new();
        for decoder in &decoders {
            let width = u64_field(decoder.get("width"), "decoder width")?;
            *widths.entry(width).or_default() += 1;
        }
        let width = widths
            .iter()
            .max_by_key(|(width, count)| (**count, std::cmp::Reverse(**width)))
            .map(|(width, _)| *width)
            .context("linked decoder group has no widths")?;
        let width_usize = usize::try_from(width).context("decoder width does not fit usize")?;
        if width_usize == 0 {
            bail!("decoder width must be non-zero");
        }
        let values = values(builder)?;
        let unknowns = unknown_map(builder)?;
        let mut instructions = Vec::new();
        let mut resolved = 0_usize;
        let mut known_opcodes = BTreeSet::new();
        for (index, chunk) in values.chunks(width_usize).enumerate() {
            let pc = index * width_usize;
            let fields = (0..chunk.len())
                .map(|offset| symbolic_field(values, &unknowns, pc + offset, &aliases))
                .collect::<Vec<_>>();
            resolved += fields
                .iter()
                .filter(|field| {
                    matches!(
                        field.get("kind").and_then(Value::as_str),
                        Some("literal" | "folded")
                    )
                })
                .count();
            if let Some(opcode) = fields
                .first()
                .and_then(|field| field.get("value"))
                .and_then(Value::as_u64)
            {
                known_opcodes.insert(opcode);
            }
            instructions.push(json!({
                "pc": pc,
                "index": index,
                "opcode": fields.first().cloned().unwrap_or(Value::Null),
                "operands": fields.into_iter().skip(1).collect::<Vec<_>>(),
                "complete": chunk.len() == width_usize,
            }));
        }
        let total_u32 = u32::try_from(values.len()).context("stream too large for ratio")?;
        let resolved_u32 =
            u32::try_from(resolved).context("resolved field count too large for ratio")?;
        let ratio = if total_u32 == 0 {
            0.0
        } else {
            f64::from(resolved_u32) / f64::from(total_u32)
        };
        let decoder_functions = decoders
            .iter()
            .filter_map(|decoder| decoder.get("function_id").and_then(Value::as_str))
            .collect::<BTreeSet<_>>();
        let decoder_objects = decoders
            .iter()
            .filter_map(|decoder| decoder.get("object").and_then(Value::as_str))
            .collect::<BTreeSet<_>>();
        let ips = decoders
            .iter()
            .filter_map(|decoder| decoder.get("ip").and_then(Value::as_str))
            .collect::<BTreeSet<_>>();
        streams.push(json!({
            "builder_start": key.0,
            "builder_end": key.1,
            "receiver": builder.get("receiver").cloned().unwrap_or(Value::Null),
            "arguments": builder.get("arguments").cloned().unwrap_or(Value::Null),
            "decoder_width": width,
            "decoder_count": decoders.len(),
            "decoder_functions": decoder_functions,
            "decoder_objects": decoder_objects,
            "ips": ips,
            "literal_arguments": values.iter().filter(|value| !value.is_null()).count(),
            "resolved_arguments": resolved,
            "resolved_ratio": ratio,
            "unknown_arguments": values.len().saturating_sub(resolved),
            "parseint_aliases": aliases,
            "opcode_known": instructions.iter().filter(|instruction| instruction.get("opcode").and_then(|op| op.get("value")).is_some()).count(),
            "opcode_unique": known_opcodes.len(),
            "instructions": instructions,
        }));
    }

    let document = json!({
        "file": report.get("file").cloned().unwrap_or_else(|| json!(file.display().to_string())),
        "streams": streams,
    });
    if let Some(path) = output {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).with_context(|| format!("creating {}", parent.display()))?;
        }
        let mut text = serde_json::to_string_pretty(&document)?;
        text.push('\n');
        fs::write(path, text).with_context(|| format!("writing {}", path.display()))?;
    }

    let streams = document
        .get("streams")
        .and_then(Value::as_array)
        .context("generated streams must be an array")?;
    println!("{}: {} linked streams", file.display(), streams.len());
    let mut ordered = streams.iter().collect::<Vec<_>>();
    ordered.sort_by_key(|stream| {
        std::cmp::Reverse(
            stream
                .get("arguments")
                .and_then(Value::as_u64)
                .unwrap_or_default(),
        )
    });
    for stream in ordered.into_iter().take(preview) {
        println!(
            "  @{:x}-{:x} args={} width={} resolved={:.1}% opcodes={} ips={}",
            stream
                .get("builder_start")
                .and_then(Value::as_u64)
                .unwrap_or_default(),
            stream
                .get("builder_end")
                .and_then(Value::as_u64)
                .unwrap_or_default(),
            stream
                .get("arguments")
                .and_then(Value::as_u64)
                .unwrap_or_default(),
            stream
                .get("decoder_width")
                .and_then(Value::as_u64)
                .unwrap_or_default(),
            stream
                .get("resolved_ratio")
                .and_then(Value::as_f64)
                .unwrap_or_default()
                * 100.0,
            stream
                .get("opcode_unique")
                .and_then(Value::as_u64)
                .unwrap_or_default(),
            stream
                .get("ips")
                .and_then(Value::as_array)
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
                .collect::<Vec<_>>()
                .join(",")
        );
        for instruction in stream
            .get("instructions")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .take(3)
        {
            let mut fields = Vec::new();
            if let Some(opcode) = instruction.get("opcode") {
                fields.push(render_symbolic(opcode));
            }
            fields.extend(
                instruction
                    .get("operands")
                    .and_then(Value::as_array)
                    .into_iter()
                    .flatten()
                    .map(render_symbolic),
            );
            println!(
                "    {:04x}: {}",
                instruction
                    .get("pc")
                    .and_then(Value::as_u64)
                    .unwrap_or_default(),
                fields.join(" | ")
            );
        }
    }
    if output.is_none() {
        let mut text = serde_json::to_string_pretty(&document)?;
        text.push('\n');
        print!("{text}");
    }
    Ok(())
}

fn render_symbolic(field: &Value) -> String {
    match field.get("kind").and_then(Value::as_str) {
        Some("literal") => field
            .get("value")
            .map_or_else(|| "?".to_owned(), Value::to_string),
        Some("folded") | Some("symbolic") => field
            .get("expr")
            .and_then(Value::as_str)
            .unwrap_or("?")
            .to_owned(),
        _ => "?".to_owned(),
    }
}
