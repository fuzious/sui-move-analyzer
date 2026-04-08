use clap::{Parser, ValueEnum};
use serde::{Deserialize, Serialize};
use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
    process::Command,
};
use sui_move_analyzer::{implicit_deps, security_analysis::analyze_package};

#[derive(Parser, Debug)]
#[command(author, version, about = "Run the security analyzer against a pinned external corpus")]
struct Options {
    #[arg(long)]
    manifest: PathBuf,

    #[arg(long, value_enum, default_value_t = OutputFormat::Table)]
    format: OutputFormat,
}

#[derive(Clone, Copy, Debug, ValueEnum)]
enum OutputFormat {
    Table,
    Json,
}

#[derive(Debug, Deserialize)]
struct CorpusManifest {
    packages: Vec<CorpusPackage>,
}

#[derive(Debug, Deserialize)]
struct CorpusPackage {
    label: String,
    git: String,
    rev: String,
    package_subdir: String,
    with_implicit_deps: Option<bool>,
    expected: String,
}

#[derive(Debug, Serialize)]
struct CorpusResult {
    label: String,
    git: String,
    rev: String,
    package_subdir: String,
    expected: String,
    actual: String,
    finding_count: usize,
    rule_ids: Vec<String>,
    error: Option<String>,
}

fn main() -> anyhow::Result<()> {
    let options = Options::parse();
    let manifest: CorpusManifest = toml::from_str(&fs::read_to_string(&options.manifest)?)?;
    let cache_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("security_corpus");
    fs::create_dir_all(&cache_root)?;

    let mut results = vec![];
    for package in manifest.packages {
        eprintln!(
            "[security_corpus] analyzing {} @ {} ({})",
            package.label,
            short_rev(&package.rev),
            package.package_subdir
        );
        results.push(run_package(&cache_root, &package));
    }

    match options.format {
        OutputFormat::Json => {
            println!("{}", serde_json::to_string_pretty(&results)?);
        }
        OutputFormat::Table => {
            println!("label | expected | actual | findings | rules | revision");
            for result in &results {
                println!(
                    "{} | {} | {} | {} | {} | {}",
                    result.label,
                    result.expected,
                    result.actual,
                    result.finding_count,
                    if result.rule_ids.is_empty() {
                        "-".to_string()
                    } else {
                        result.rule_ids.join(",")
                    },
                    short_rev(&result.rev)
                );
                if let Some(error) = &result.error {
                    println!("  error: {error}");
                }
            }
        }
    }

    Ok(())
}

fn run_package(cache_root: &Path, package: &CorpusPackage) -> CorpusResult {
    let repo_dir = cache_root.join(sanitize_label(&package.label));
    let package_path = repo_dir.join(&package.package_subdir);
    let mut result = CorpusResult {
        label: package.label.clone(),
        git: package.git.clone(),
        rev: package.rev.clone(),
        package_subdir: package.package_subdir.clone(),
        expected: package.expected.clone(),
        actual: "manual-review".to_string(),
        finding_count: 0,
        rule_ids: vec![],
        error: None,
    };

    if let Err(error) = checkout_repo(&repo_dir, &package.git, &package.rev) {
        result.error = Some(error.to_string());
        return result;
    }

    let deps = if package.with_implicit_deps.unwrap_or(false) {
        implicit_deps()
    } else {
        Default::default()
    };

    match analyze_package(&package_path, deps) {
        Ok(analysis) => {
            let mut rules = BTreeSet::new();
            for finding in &analysis.findings {
                rules.insert(finding.kind.rule_id().to_string());
            }
            result.finding_count = analysis.findings.len();
            result.rule_ids = rules.into_iter().collect();
            result.actual = if analysis.findings.is_empty() {
                "clean".to_string()
            } else {
                "flagged".to_string()
            };
        }
        Err(error) => {
            result.error = Some(error.to_string());
        }
    }

    result
}

fn checkout_repo(repo_dir: &Path, git: &str, rev: &str) -> anyhow::Result<()> {
    if !repo_dir.exists() {
        run_git(None, &["clone", "--no-checkout", git, repo_dir.to_str().unwrap()])?;
    }
    run_git(Some(repo_dir), &["fetch", "--depth", "1", "origin", rev])?;
    run_git(Some(repo_dir), &["checkout", "--force", rev])?;
    Ok(())
}

fn run_git(cwd: Option<&Path>, args: &[&str]) -> anyhow::Result<()> {
    let mut command = Command::new("git");
    command.args(args);
    if let Some(cwd) = cwd {
        command.current_dir(cwd);
    }
    let output = command.output()?;
    if output.status.success() {
        Ok(())
    } else {
        anyhow::bail!(
            "git {} failed: {}",
            args.join(" "),
            String::from_utf8_lossy(&output.stderr)
        )
    }
}

fn sanitize_label(label: &str) -> String {
    label
        .chars()
        .map(|char| if char.is_ascii_alphanumeric() { char } else { '_' })
        .collect()
}

fn short_rev(rev: &str) -> &str {
    rev.get(..7).unwrap_or(rev)
}
