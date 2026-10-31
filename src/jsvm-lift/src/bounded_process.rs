use anyhow::{Context, Result};
#[cfg(unix)]
use std::os::unix::process::CommandExt;
use std::{
    fs,
    path::Path,
    process::{Command, Stdio},
    time::Duration,
};
use wait_timeout::ChildExt;

#[derive(Debug)]
pub(crate) struct CommandResult {
    pub(crate) code: i32,
    pub(crate) stdout: Vec<u8>,
    pub(crate) stderr: Vec<u8>,
}

pub(crate) fn run_command_with_timeout(
    command: &mut Command,
    work: &Path,
    timeout: Duration,
) -> Result<CommandResult> {
    fs::create_dir_all(work).with_context(|| format!("creating {}", work.display()))?;
    let stdout_path = work.join("stdout.log");
    let stderr_path = work.join("stderr.log");
    let stdout = fs::File::create(&stdout_path)
        .with_context(|| format!("creating {}", stdout_path.display()))?;
    let stderr = fs::File::create(&stderr_path)
        .with_context(|| format!("creating {}", stderr_path.display()))?;
    let rendered = format!("{command:?}");
    #[cfg(unix)]
    command.process_group(0);
    let mut child = command
        .stdout(Stdio::from(stdout))
        .stderr(Stdio::from(stderr))
        .spawn()
        .with_context(|| format!("launching {rendered}"))?;
    let (status, timed_out) = match child
        .wait_timeout(timeout)
        .with_context(|| format!("waiting for {rendered}"))?
    {
        Some(status) => (status, false),
        None => {
            #[cfg(unix)]
            {
                let group = format!("-{}", child.id());
                let killed_group = Command::new("kill")
                    .arg("-KILL")
                    .arg("--")
                    .arg(group)
                    .status()
                    .is_ok_and(|status| status.success());
                if !killed_group && child.try_wait()?.is_none() {
                    child
                        .kill()
                        .with_context(|| format!("killing timed-out {rendered}"))?;
                }
            }
            #[cfg(not(unix))]
            child
                .kill()
                .with_context(|| format!("killing timed-out {rendered}"))?;
            (
                child
                    .wait()
                    .with_context(|| format!("reaping timed-out {rendered}"))?,
                true,
            )
        }
    };
    let stdout =
        fs::read(&stdout_path).with_context(|| format!("reading {}", stdout_path.display()))?;
    let mut stderr =
        fs::read(&stderr_path).with_context(|| format!("reading {}", stderr_path.display()))?;
    if timed_out {
        stderr.extend_from_slice(format!("\ntimed out after {}s", timeout.as_secs()).as_bytes());
    }
    Ok(CommandResult {
        code: if timed_out {
            124
        } else {
            status.code().unwrap_or(1)
        },
        stdout,
        stderr,
    })
}

#[must_use]
pub(crate) fn command_error(output: &CommandResult) -> String {
    let mut bytes = Vec::with_capacity(output.stdout.len() + output.stderr.len());
    bytes.extend_from_slice(&output.stdout);
    bytes.extend_from_slice(&output.stderr);
    let start = bytes.len().saturating_sub(3000);
    String::from_utf8_lossy(&bytes[start..]).into_owned()
}
