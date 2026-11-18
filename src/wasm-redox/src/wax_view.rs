//! Best-effort Wax high-level rendering shared by standalone and project WASM views.
use anyhow::{Context, Result};
use std::{fs, io::ErrorKind, path::Path, process::Command};
use work_budget::{run_command, CommandRunError, WorkBudget};

#[derive(Debug, Clone, Copy)]
pub enum WaxViewOrigin {
    Standalone,
    ProjectMaterialization,
}

/// Execute Wax within the supplied work budget and preserve the folded-WAT
/// fallback when Wax is absent or returns a nonzero status.
///
/// # Errors
///
/// Returns errors for a failed process invocation other than Wax-not-found,
/// budget exhaustion, or failure to persist a successfully rendered view.
pub fn write_wax_view(
    binary: &Path,
    output: &Path,
    wax: &Path,
    budget: &WorkBudget,
    origin: WaxViewOrigin,
) -> Result<()> {
    let (label, run_verb, write_verb) = match origin {
        WaxViewOrigin::Standalone => ("wasm-redox", "run", "write"),
        WaxViewOrigin::ProjectMaterialization => ("wasm-materialize", "running", "writing"),
    };

    let mut command = Command::new(wax);
    command.arg(binary);
    let result = match run_command(&mut command, budget) {
        Ok(result) => result,
        Err(CommandRunError::Spawn(error)) if error.kind() == ErrorKind::NotFound => {
            eprintln!(
                "{label}: Wax not found at {}; skipping high-level view",
                wax.display()
            );
            return Ok(());
        }
        Err(error) => return Err(error).with_context(|| format!("{run_verb} {}", wax.display())),
    };
    if !result.status.success() {
        eprintln!(
            "{label}: Wax failed for {} ({}); keeping folded WAT fallback\n{}",
            binary.display(),
            result.status,
            String::from_utf8_lossy(&result.stderr)
        );
        return Ok(());
    }
    fs::write(output, result.stdout).with_context(|| format!("{write_verb} {}", output.display()))
}
