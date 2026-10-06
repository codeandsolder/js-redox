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

pub fn read_jsonl<T: DeserializeOwned>(path: &Path) -> Result<Vec<T>> {
    let text = fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;
    text.lines()
        .enumerate()
        .filter(|(_, line)| !line.trim().is_empty())
        .map(|(index, line)| {
            serde_json::from_str(line)
                .with_context(|| format!("parsing {} line {}", path.display(), index + 1))
        })
        .collect()
}
