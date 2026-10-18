pub mod fresh_eval;
pub mod state_machine;

use anyhow::{Context, Result};
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use wasmparser::{ExternalKind, Operator, Parser, Payload, TypeRef, Validator, WasmFeatures};

fn lowercase_hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        out.push(char::from(HEX[usize::from(byte >> 4)]));
        out.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    out
}

#[derive(Debug, Serialize)]
pub struct ImportSummary {
    pub module: String,
    pub name: String,
    pub kind: String,
}

#[derive(Debug, Serialize)]
pub struct ExportSummary {
    pub name: String,
    pub kind: String,
    pub index: u32,
}

#[derive(Debug, Serialize)]
pub struct FunctionSummary {
    pub index: u32,
    pub body_bytes: usize,
    pub exports: Vec<String>,
    pub role: &'static str,
    pub direct_calls: Vec<u32>,
    pub reachable_from_exports: Vec<String>,
}

#[derive(Debug, Serialize)]
pub struct ExportReachability {
    pub export: String,
    pub function_index: u32,
    pub reachable_functions: Vec<u32>,
}

#[derive(Debug, Serialize)]
pub struct CallGraphSummary {
    pub direct_edges: usize,
    pub exports: Vec<ExportReachability>,
}

#[derive(Debug, Default, Serialize)]
pub struct SectionCounts {
    pub types: u32,
    pub imported_functions: u32,
    pub defined_functions: u32,
    pub tables: u32,
    pub memories: u32,
    pub globals: u32,
    pub elements: u32,
    pub data_segments: u32,
}

#[derive(Debug, Serialize)]
pub struct DeepExportAnalysis {
    pub export: String,
    pub function_index: u32,
    pub body_bytes: usize,
    pub analysis: Option<state_machine::ExportSemanticAnalysis>,
    pub error: Option<String>,
}

#[derive(Debug, Serialize)]
pub struct DeepModuleReport {
    pub schema: &'static str,
    pub exports: Vec<DeepExportAnalysis>,
}

#[derive(Debug, Serialize)]
pub struct ModuleReport {
    pub sha256: String,
    pub byte_len: usize,
    pub sections: SectionCounts,
    pub imports: Vec<ImportSummary>,
    pub exports: Vec<ExportSummary>,
    pub functions: Vec<FunctionSummary>,
    pub call_graph: CallGraphSummary,
    pub custom_sections: Vec<String>,
    pub strings: Vec<String>,
}

fn import_kind(ty: TypeRef) -> &'static str {
    match ty {
        TypeRef::Func(_) | TypeRef::FuncExact(_) => "function",
        TypeRef::Table(_) => "table",
        TypeRef::Memory(_) => "memory",
        TypeRef::Global(_) => "global",
        TypeRef::Tag(_) => "tag",
    }
}

fn export_kind(kind: ExternalKind) -> &'static str {
    match kind {
        ExternalKind::Func | ExternalKind::FuncExact => "function",
        ExternalKind::Table => "table",
        ExternalKind::Memory => "memory",
        ExternalKind::Global => "global",
        ExternalKind::Tag => "tag",
    }
}

fn classify_function(exports: &[String]) -> &'static str {
    if exports
        .iter()
        .any(|name| name.starts_with("__wbindgen") || name.starts_with("__wbg"))
    {
        "binding_glue"
    } else if exports.is_empty() {
        "internal"
    } else {
        "exported_core"
    }
}

fn extract_ascii_strings(bytes: &[u8]) -> Vec<String> {
    const MIN_LEN: usize = 6;
    const MAX_STRINGS: usize = 512;
    const MAX_STRING_LEN: usize = 512;

    let mut result = Vec::new();
    let mut start = None;

    for (index, byte) in bytes.iter().copied().chain(std::iter::once(0)).enumerate() {
        let printable = byte.is_ascii_graphic() || byte == b' ';
        if printable {
            start.get_or_insert(index);
            continue;
        }
        let Some(begin) = start.take() else {
            continue;
        };
        let end = index;
        if end.saturating_sub(begin) < MIN_LEN || begin >= bytes.len() {
            continue;
        }
        let bounded_end = end
            .min(begin.saturating_add(MAX_STRING_LEN))
            .min(bytes.len());
        if let Ok(text) = std::str::from_utf8(&bytes[begin..bounded_end]) {
            result.push(text.to_owned());
            if result.len() >= MAX_STRINGS {
                break;
            }
        }
    }
    result
}

pub fn analyze(bytes: &[u8]) -> Result<ModuleReport> {
    Validator::new_with_features(WasmFeatures::all())
        .validate_all(bytes)
        .context("validate WebAssembly")?;

    let digest = Sha256::digest(bytes);
    let mut sections = SectionCounts::default();
    let mut imports = Vec::new();
    let mut exports = Vec::new();
    let mut custom_sections = Vec::new();
    let mut function_exports: BTreeMap<u32, Vec<String>> = BTreeMap::new();
    let mut functions = Vec::new();
    let mut next_defined_function = None;

    for payload in Parser::new(0).parse_all(bytes) {
        match payload.context("parse WebAssembly payload")? {
            Payload::TypeSection(reader) => sections.types = reader.count(),
            Payload::ImportSection(reader) => {
                for group in reader {
                    for import in group.context("parse import group")?.into_iter() {
                        let (_, import) = import.context("parse import")?;
                        let kind = import_kind(import.ty);
                        if kind == "function" {
                            sections.imported_functions =
                                sections.imported_functions.saturating_add(1);
                        }
                        imports.push(ImportSummary {
                            module: import.module.to_owned(),
                            name: import.name.to_owned(),
                            kind: kind.to_owned(),
                        });
                    }
                }
            }
            Payload::FunctionSection(reader) => {
                sections.defined_functions = reader.count();
                next_defined_function = Some(sections.imported_functions);
            }
            Payload::TableSection(reader) => sections.tables = reader.count(),
            Payload::MemorySection(reader) => sections.memories = reader.count(),
            Payload::GlobalSection(reader) => sections.globals = reader.count(),
            Payload::ElementSection(reader) => sections.elements = reader.count(),
            Payload::DataSection(reader) => sections.data_segments = reader.count(),
            Payload::ExportSection(reader) => {
                for export in reader {
                    let export = export.context("parse export")?;
                    let kind = export_kind(export.kind);
                    if kind == "function" {
                        function_exports
                            .entry(export.index)
                            .or_default()
                            .push(export.name.to_owned());
                    }
                    exports.push(ExportSummary {
                        name: export.name.to_owned(),
                        kind: kind.to_owned(),
                        index: export.index,
                    });
                }
            }
            Payload::CodeSectionEntry(body) => {
                let index = next_defined_function
                    .context("code section encountered without function section")?;
                let export_names = function_exports.remove(&index).unwrap_or_default();
                let range = body.range();
                let body_bytes = usize::try_from(range.end.saturating_sub(range.start))
                    .context("function body length does not fit usize")?;
                let mut direct_calls = BTreeSet::new();
                let mut operators = body
                    .get_operators_reader()
                    .context("read function operators")?;
                while !operators.eof() {
                    match operators.read().context("read function operator")? {
                        Operator::Call { function_index }
                        | Operator::ReturnCall { function_index } => {
                            direct_calls.insert(function_index);
                        }
                        _ => {}
                    }
                }
                functions.push(FunctionSummary {
                    index,
                    body_bytes,
                    role: classify_function(&export_names),
                    exports: export_names,
                    direct_calls: direct_calls.into_iter().collect(),
                    reachable_from_exports: Vec::new(),
                });
                next_defined_function = Some(index.saturating_add(1));
            }
            Payload::CustomSection(reader) => {
                custom_sections.push(reader.name().to_owned());
            }
            _ => {}
        }
    }

    let adjacency = functions
        .iter()
        .map(|function| (function.index, function.direct_calls.clone()))
        .collect::<BTreeMap<_, _>>();
    let direct_edges = adjacency.values().map(Vec::len).sum();
    let function_exports = exports
        .iter()
        .filter(|export| export.kind == "function")
        .map(|export| (export.name.clone(), export.index))
        .collect::<Vec<_>>();
    let mut export_reachability = Vec::new();
    for (export_name, root) in function_exports {
        let mut queue = VecDeque::from([root]);
        let mut reachable = BTreeSet::new();
        while let Some(function_index) = queue.pop_front() {
            if !reachable.insert(function_index) {
                continue;
            }
            if let Some(callees) = adjacency.get(&function_index) {
                queue.extend(callees.iter().copied());
            }
        }
        for function in &mut functions {
            if reachable.contains(&function.index) {
                function.reachable_from_exports.push(export_name.clone());
            }
        }
        export_reachability.push(ExportReachability {
            export: export_name,
            function_index: root,
            reachable_functions: reachable.into_iter().collect(),
        });
    }

    Ok(ModuleReport {
        sha256: lowercase_hex(digest.as_ref()),
        byte_len: bytes.len(),
        sections,
        imports,
        exports,
        functions,
        call_graph: CallGraphSummary {
            direct_edges,
            exports: export_reachability,
        },
        custom_sections,
        strings: extract_ascii_strings(bytes),
    })
}

pub fn deep_analyze(bytes: &[u8], report: &ModuleReport) -> DeepModuleReport {
    let mut exports = Vec::new();
    for function in &report.functions {
        if function.role != "exported_core" || function.body_bytes < 128 {
            continue;
        }
        let Some(export) = function.exports.first() else {
            continue;
        };
        match state_machine::analyze_export_semantics(bytes, export) {
            Ok(analysis) => exports.push(DeepExportAnalysis {
                export: export.clone(),
                function_index: function.index,
                body_bytes: function.body_bytes,
                analysis: Some(analysis),
                error: None,
            }),
            Err(error) => exports.push(DeepExportAnalysis {
                export: export.clone(),
                function_index: function.index,
                body_bytes: function.body_bytes,
                analysis: None,
                error: Some(format!("{error:#}")),
            }),
        }
    }
    DeepModuleReport {
        schema: "wasm-redox/deep-v8",
        exports,
    }
}

pub fn folded_wat(bytes: &[u8]) -> Result<String> {
    let mut config = wasmprinter::Config::new();
    config.name_unnamed(true).fold_instructions(true);
    let mut output = String::new();
    config
        .print(bytes, &mut wasmprinter::PrintFmtWrite(&mut output))
        .context("print folded WAT")?;
    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reports_and_prints_small_module() -> Result<()> {
        let bytes = wat::parse_str(
            r#"(module
                (import "env" "tick" (func))
                (func (export "add") (param i32 i32) (result i32)
                    local.get 0
                    local.get 1
                    i32.add)
            )"#,
        )?;
        let report = analyze(&bytes)?;
        assert_eq!(deep_analyze(&bytes, &report).schema, "wasm-redox/deep-v8");
        assert_eq!(report.sections.imported_functions, 1);
        assert_eq!(report.sections.defined_functions, 1);
        assert_eq!(report.functions.len(), 1);
        assert_eq!(report.functions[0].exports, ["add"]);
        assert_eq!(report.functions[0].role, "exported_core");
        assert_eq!(report.functions[0].direct_calls, Vec::<u32>::new());
        assert_eq!(report.call_graph.exports.len(), 1);
        assert_eq!(report.call_graph.exports[0].export, "add");
        assert_eq!(report.call_graph.exports[0].reachable_functions, [1]);

        let readable = folded_wat(&bytes)?;
        assert!(readable.contains("i32.add"));
        assert!(readable.contains("(export \"add\""));
        Ok(())
    }
}
