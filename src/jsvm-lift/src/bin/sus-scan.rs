use anyhow::Result;
use clap::Parser as ClapParser;
use jsvm_lift::sus_scan::{
    build_report, collect_input_paths, scan_file, SusScanOptions, SusScanReport,
};
use std::path::PathBuf;

#[derive(ClapParser, Debug)]
#[command(
    about = "Fast explainable triage for dense clusters of obfuscation/packing-like JavaScript structures"
)]
struct Args {
    /// JavaScript files or directories to scan recursively.
    #[arg(required = true)]
    inputs: Vec<PathBuf>,

    /// Emit one JSON report instead of human-readable text.
    #[arg(long)]
    json: bool,

    /// Maximum byte span considered one suspicious cluster.
    #[arg(long, default_value_t = 3072)]
    window_bytes: usize,

    /// Minimum cluster score to report.
    #[arg(long, default_value_t = 12)]
    min_score: u32,

    /// Minimum number of evidence points in a reported cluster.
    #[arg(long, default_value_t = 3)]
    min_signals: usize,

    /// Maximum clusters reported per file.
    #[arg(long, default_value_t = 20)]
    max_clusters: usize,

    /// Minimum string length for opaque/base64 blob heuristics.
    #[arg(long, default_value_t = 96)]
    blob_min_len: usize,

    /// Include every raw evidence point in JSON, not only clustered evidence.
    #[arg(long)]
    include_signals: bool,
}

fn print_text(report: &SusScanReport) {
    for file in report.files.iter().filter(|file| !file.clusters.is_empty()) {
        println!(
            "\n{}  bytes={} signals={} top_score={} diagnostics={} decode={}{}{}{}",
            file.input,
            file.bytes,
            file.signal_count,
            file.top_score,
            file.diagnostics,
            file.decode_encoding,
            if file.decode_had_errors {
                " DECODE_ERRORS"
            } else {
                ""
            },
            if file.decode_uncertain {
                " DECODE_UNCERTAIN"
            } else {
                ""
            },
            if file.fatal_error {
                " FATAL_PARSE_ERROR"
            } else {
                ""
            }
        );
        for (index, cluster) in file.clusters.iter().enumerate() {
            let kinds = cluster
                .kinds
                .iter()
                .map(|(kind, count)| format!("{kind}×{count}"))
                .collect::<Vec<_>>()
                .join(", ");
            let repeated = if cluster.repeated_subjects.is_empty() {
                String::new()
            } else {
                format!(
                    " repeated=[{}]",
                    cluster
                        .repeated_subjects
                        .iter()
                        .take(4)
                        .map(|item| format!("{}×{}", item.subject, item.count))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            };
            println!(
                "  #{:<2} score={:<3} density={:>6.1}/KiB L{}-{} @{:x}-{:x} signals={} {}{}",
                index + 1,
                cluster.score,
                cluster.density_per_kib,
                cluster.start_line,
                cluster.end_line,
                cluster.start,
                cluster.end,
                cluster.signal_count,
                kinds,
                repeated,
            );
            for signal in cluster.signals.iter().take(6) {
                println!(
                    "       w{:<2} L{:<5} {:<24} {}{}",
                    signal.weight,
                    signal.line,
                    signal.kind,
                    signal.detail,
                    signal
                        .subject
                        .as_deref()
                        .map(|subject| format!(" [{subject}]"))
                        .unwrap_or_default()
                );
            }
            if cluster.signals.len() > 6 {
                println!(
                    "       … {} more evidence point(s)",
                    cluster.signals.len() - 6
                );
            }
            println!("       {}", cluster.snippet);
        }
    }
    println!(
        "\nSUS summary: {} file(s) scanned; {} parse-recovered; {} incomplete; {} fatal; {} with clusters; {} cluster(s)",
        report.files_scanned,
        report.files_with_parse_recovery,
        report.files_with_incomplete_analysis,
        report.files_with_fatal_error,
        report.files_with_clusters,
        report.total_clusters
    );
}

fn main() -> Result<()> {
    let args = Args::parse();
    if args.window_bytes < 64 {
        anyhow::bail!("--window-bytes must be at least 64");
    }
    let options = SusScanOptions {
        window_bytes: args.window_bytes,
        min_score: args.min_score,
        min_signals: args.min_signals,
        max_clusters: args.max_clusters,
        blob_min_len: args.blob_min_len,
        include_signals: args.include_signals,
    };
    options.validate()?;

    let paths = collect_input_paths(&args.inputs)?;

    let mut files = Vec::with_capacity(paths.len());
    for path in &paths {
        files.push(scan_file(path, &options)?);
    }
    let report = build_report(files, &options)?;

    if args.json {
        println!("{}", serde_json::to_string(&report)?);
    } else {
        print_text(&report);
    }
    Ok(())
}
