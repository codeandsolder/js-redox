use anyhow::{Context, Result};
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use wasmparser::{ExternalKind, Parser, Payload, TypeRef, Validator, WasmFeatures};

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
pub struct ModuleReport {
    pub sha256: String,
    pub byte_len: usize,
    pub sections: SectionCounts,
    pub imports: Vec<ImportSummary>,
    pub exports: Vec<ExportSummary>,
    pub functions: Vec<FunctionSummary>,
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
                functions.push(FunctionSummary {
                    index,
                    body_bytes,
                    role: classify_function(&export_names),
                    exports: export_names,
                });
                next_defined_function = Some(index.saturating_add(1));
            }
            Payload::CustomSection(reader) => {
                custom_sections.push(reader.name().to_owned());
            }
            _ => {}
        }
    }

    Ok(ModuleReport {
        sha256: format!("{digest:x}"),
        byte_len: bytes.len(),
        sections,
        imports,
        exports,
        functions,
        custom_sections,
        strings: extract_ascii_strings(bytes),
    })
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
        assert_eq!(report.sections.imported_functions, 1);
        assert_eq!(report.sections.defined_functions, 1);
        assert_eq!(report.functions.len(), 1);
        assert_eq!(report.functions[0].exports, ["add"]);
        assert_eq!(report.functions[0].role, "exported_core");

        let readable = folded_wat(&bytes)?;
        assert!(readable.contains("i32.add"));
        assert!(readable.contains("(export \"add\""));
        Ok(())
    }
}
