use anyhow::{bail, Context, Result};
use std::{env, path::PathBuf};

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

pub fn tool_dir() -> Result<PathBuf> {
    let executable = env::current_exe().context("locating current executable")?;
    executable
        .parent()
        .map(|path| path.to_path_buf())
        .context("current executable has no parent directory")
}

pub fn sibling_tool(name: &str) -> Result<PathBuf> {
    Ok(tool_dir()?.join(name))
}
