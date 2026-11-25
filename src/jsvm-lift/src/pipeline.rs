use anyhow::{Context, Result};
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use std::{collections::BTreeMap, fs, path::Path};

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct RoleAssignment {
    pub name: String,
    pub source: String,
    pub votes: Option<i64>,
    pub margin: Option<i64>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct VmRoles {
    pub file: String,
    pub decoder: String,
    pub matched_paths: usize,
    pub roles: BTreeMap<String, RoleAssignment>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct BindingInfo {
    pub original: String,
    pub normalized: String,
    pub source: String,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct NormalizedPath {
    pub guards: Vec<String>,
    pub states: Vec<u64>,
    pub effects: Vec<String>,
    pub terminal: Option<String>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct NormalizedOpcode {
    pub opcode: u64,
    pub derived_env: BTreeMap<String, serde_json::Value>,
    pub paths: Vec<NormalizedPath>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct NormalizedVm {
    pub file: String,
    pub decoder: String,
    pub parent: String,
    pub role_bindings: BTreeMap<String, BindingInfo>,
    pub state_machine: serde_json::Value,
    pub opcodes: Vec<NormalizedOpcode>,
}

/// Read a stream of JSON records (including a single pretty-printed report).
///
/// # Errors
///
/// Fails if the input cannot be read as UTF-8 or a JSON record is malformed; the parse error includes the file and record number.
pub fn read_json_records<T: DeserializeOwned>(path: &Path) -> Result<Vec<T>> {
    let text = fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;
    serde_json::Deserializer::from_str(&text)
        .into_iter::<T>()
        .enumerate()
        .map(|(index, result)| {
            result.with_context(|| format!("parsing {} record {}", path.display(), index + 1))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn records_support_pretty_printed_and_compact_reports() -> Result<()> {
        let workspace = tempfile::tempdir()?;
        let path = workspace.path().join("reports.json");
        fs::write(&path, "{\n  \"value\": 1\n}\n{\"value\":2}\n")?;
        let values: Vec<serde_json::Value> = read_json_records(&path)?;
        assert_eq!(
            values,
            vec![
                serde_json::json!({"value": 1}),
                serde_json::json!({"value": 2})
            ]
        );
        fs::write(&path, "{\"value\":1}\n{")?;
        assert!(read_json_records::<serde_json::Value>(&path).is_err());
        Ok(())
    }
}
