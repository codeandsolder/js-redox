use anyhow::{bail, Context, Result};
use clap::Parser as ClapParser;
use jsvm_lift::source_directive::{source_directives, SourceDirective};
use serde::Serialize;
use std::{
    fs,
    io::{self, Read},
    path::PathBuf,
};

#[derive(ClapParser, Debug)]
#[command(about = "Extract sourceURL/sourceMappingURL directives from actual JavaScript comments")]
struct Args {
    #[arg(long, conflicts_with = "inputs")]
    stdin: bool,
    #[arg(value_name = "INPUT")]
    inputs: Vec<PathBuf>,
}

#[derive(Debug, Serialize)]
struct FileDirectives {
    input: String,
    directives: Vec<SourceDirective>,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let mut results = Vec::new();

    if args.stdin {
        let mut source = String::new();
        io::stdin()
            .read_to_string(&mut source)
            .context("reading JavaScript from stdin")?;
        results.push(FileDirectives {
            input: "-".to_string(),
            directives: source_directives(&source),
        });
    } else {
        if args.inputs.is_empty() {
            bail!("provide at least one INPUT or use --stdin");
        }
        for input in args.inputs {
            let source = fs::read_to_string(&input)
                .with_context(|| format!("reading {}", input.display()))?;
            results.push(FileDirectives {
                input: input.display().to_string(),
                directives: source_directives(&source),
            });
        }
    }

    println!("{}", serde_json::to_string(&results)?);
    Ok(())
}
