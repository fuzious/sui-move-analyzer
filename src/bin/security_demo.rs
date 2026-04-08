use clap::Parser;
use std::path::PathBuf;
use sui_move_analyzer::{
    discover_manifest_and_kind, implicit_deps,
    security_analysis::analyze_package,
};

#[derive(Parser, Debug)]
#[command(author, version, about = "Run the Sui Move security shift analysis demo")]
struct Options {
    /// Path to a Move package directory or any .move file inside it
    path: PathBuf,

    /// Include the analyzer's implicit Sui framework dependency overrides
    #[arg(long)]
    with_implicit_deps: bool,
}

fn main() -> anyhow::Result<()> {
    let options = Options::parse();
    let package_path = package_root(&options.path)?;
    let deps = if options.with_implicit_deps {
        implicit_deps()
    } else {
        Default::default()
    };
    let analysis = analyze_package(&package_path, deps)?;

    if analysis.findings.is_empty() {
        println!("No security findings for {}", package_path.display());
        return Ok(());
    }

    println!("file | line | severity | rule | message");
    let mut rows = analysis
        .findings
        .iter()
        .map(|finding| {
            let line = analysis
                .mapped_files
                .start_position_opt(&finding.loc)
                .map(|position| position.line_offset() + 1)
                .unwrap_or(0);
            (
                analysis
                    .mapped_files
                    .file_path(&finding.loc.file_hash())
                    .display()
                    .to_string(),
                line,
                format!("{:?}", finding.severity),
                finding.kind.rule_id(),
                finding.message.clone(),
            )
        })
        .collect::<Vec<_>>();

    rows.sort_by(|left, right| {
        left.0
            .cmp(&right.0)
            .then(left.1.cmp(&right.1))
            .then(left.3.cmp(right.3))
    });

    for (file, line, severity, rule, message) in rows {
        println!("{file} | {line} | {severity} | {rule} | {message}");
    }
    Ok(())
}

fn package_root(path: &PathBuf) -> anyhow::Result<PathBuf> {
    if path.is_dir() && path.join("Move.toml").exists() {
        return Ok(path.clone());
    }
    if let Some((manifest, _)) = discover_manifest_and_kind(path) {
        return Ok(manifest);
    }
    anyhow::bail!(
        "could not find a Move.toml package root for {}",
        path.display()
    )
}
