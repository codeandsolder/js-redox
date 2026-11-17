use anyhow::{bail, Context, Result};
use std::{
    env,
    path::{Path, PathBuf},
};

/// Locate the repository root from the current directory or executable ancestors.
///
/// # Errors
///
/// Fails when the current directory or executable path cannot be determined, or when neither ancestor chain contains the expected workspace manifests.
pub fn repository_root() -> Result<PathBuf> {
    let current = env::current_dir().context("reading current directory")?;
    let executable = env::current_exe().context("locating current executable")?;
    for candidate in current.ancestors().chain(executable.ancestors()) {
        if candidate.join("Cargo.toml").is_file()
            && candidate.join("src/jsvm-lift/Cargo.toml").is_file()
        {
            return Ok(candidate.to_path_buf());
        }
    }
    bail!("could not locate js-redox repository root from cwd or executable path")
}

/// Return the directory containing the current tool executable.
///
/// # Errors
///
/// Fails when the executable path cannot be determined or has no parent directory.
pub fn tool_dir() -> Result<PathBuf> {
    let executable = env::current_exe().context("locating current executable")?;
    executable
        .parent()
        .map(Path::to_path_buf)
        .context("current executable has no parent directory")
}

/// Construct a sibling executable path relative to the current tool.
///
/// # Errors
///
/// Propagates path-resolution errors from `tool_dir`.
pub fn sibling_tool(name: &str) -> Result<PathBuf> {
    Ok(tool_dir()?.join(name))
}
