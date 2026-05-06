use clap::{Parser, ValueEnum};
use serde::{Deserialize, Serialize};
use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::mpsc,
    thread,
    time::{Duration, Instant},
};
use sui_move_analyzer::security_analysis::{
    AnalysisScope, DependencyMode, PackageAnalysisOptions, SecurityMathMode,
    analyze_package_with_options,
};

#[derive(Parser, Debug)]
#[command(
    author,
    version,
    about = "Run the security analyzer against a pinned external corpus"
)]
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
    dependency_mode: Option<ManifestDependencyMode>,
    scope: Option<ManifestAnalysisScope>,
    security_math_mode: Option<ManifestMathMode>,
    security_smt_timeout_ms: Option<u64>,
    timeout_seconds: Option<u64>,
    expected: String,
    must_include_rules: Option<Vec<String>>,
    must_exclude_rules: Option<Vec<String>>,
}

#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(rename_all = "kebab-case")]
enum ManifestDependencyMode {
    Off,
    Auto,
    Forced,
}

#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(rename_all = "kebab-case")]
enum ManifestAnalysisScope {
    Root,
    Direct,
    All,
}

#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(rename_all = "kebab-case")]
enum ManifestMathMode {
    Fast,
    Deep,
}

#[derive(Debug, Serialize)]
struct CorpusResult {
    label: String,
    git: String,
    rev: String,
    package_subdir: String,
    expected: String,
    actual: String,
    expectation: String,
    finding_count: usize,
    rule_ids: Vec<String>,
    missing_rules: Vec<String>,
    unexpected_rules: Vec<String>,
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
        let started = Instant::now();
        results.push(run_package(&cache_root, &package));
        eprintln!(
            "[security_corpus] finished {} in {:.2?}",
            package.label,
            started.elapsed()
        );
    }

    match options.format {
        OutputFormat::Json => {
            println!("{}", serde_json::to_string_pretty(&results)?);
        }
        OutputFormat::Table => {
            println!("label | expected | actual | expectation | findings | rules | revision");
            for result in &results {
                println!(
                    "{} | {} | {} | {} | {} | {} | {}",
                    result.label,
                    result.expected,
                    result.actual,
                    result.expectation,
                    result.finding_count,
                    if result.rule_ids.is_empty() {
                        "-".to_string()
                    } else {
                        result.rule_ids.join(",")
                    },
                    short_rev(&result.rev)
                );
                if !result.missing_rules.is_empty() {
                    println!("  missing rules: {}", result.missing_rules.join(","));
                }
                if !result.unexpected_rules.is_empty() {
                    println!("  unexpected rules: {}", result.unexpected_rules.join(","));
                }
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
        expectation: "manual-review".to_string(),
        finding_count: 0,
        rule_ids: vec![],
        missing_rules: vec![],
        unexpected_rules: vec![],
        error: None,
    };

    if let Err(error) = checkout_repo(&repo_dir, &package.git, &package.rev) {
        result.error = Some(error.to_string());
        return result;
    }

    let analysis_options = PackageAnalysisOptions {
        dependency_mode: match package
            .dependency_mode
            .unwrap_or(ManifestDependencyMode::Auto)
        {
            ManifestDependencyMode::Off => DependencyMode::Off,
            ManifestDependencyMode::Auto => DependencyMode::Auto,
            ManifestDependencyMode::Forced => DependencyMode::Forced,
        },
        analysis_scope: match package.scope.unwrap_or(ManifestAnalysisScope::Direct) {
            ManifestAnalysisScope::Root => AnalysisScope::RootOnly,
            ManifestAnalysisScope::Direct => AnalysisScope::RootAndDirectDeps,
            ManifestAnalysisScope::All => AnalysisScope::WholeGraph,
        },
        reuse_build_cache: true,
        security_math_mode: match package.security_math_mode.unwrap_or(ManifestMathMode::Fast) {
            ManifestMathMode::Fast => SecurityMathMode::Fast,
            ManifestMathMode::Deep => SecurityMathMode::Deep,
        },
        security_smt_timeout_ms: package.security_smt_timeout_ms.unwrap_or(250),
    };
    match analyze_with_timeout(
        package_path.clone(),
        analysis_options,
        package.timeout_seconds,
    ) {
        Ok(analysis) => {
            result.finding_count = analysis.finding_count;
            result.rule_ids = analysis.rule_ids;
            result.actual = analysis.actual;
            let actual_rules = result.rule_ids.iter().cloned().collect::<BTreeSet<_>>();
            let mut missing_rules = package
                .must_include_rules
                .clone()
                .unwrap_or_default()
                .into_iter()
                .filter(|rule| !actual_rules.contains(rule))
                .collect::<Vec<_>>();
            missing_rules.sort();
            let mut unexpected_rules = package
                .must_exclude_rules
                .clone()
                .unwrap_or_default()
                .into_iter()
                .filter(|rule| actual_rules.contains(rule))
                .collect::<Vec<_>>();
            unexpected_rules.sort();
            let status_matches = package.expected == result.actual;
            result.missing_rules = missing_rules;
            result.unexpected_rules = unexpected_rules;
            result.expectation = if status_matches
                && result.missing_rules.is_empty()
                && result.unexpected_rules.is_empty()
            {
                "matched".to_string()
            } else {
                "mismatch".to_string()
            };
        }
        Err(error) => {
            result.error = Some(error.to_string());
        }
    }

    result
}

#[derive(Debug)]
struct CorpusSummary {
    actual: String,
    finding_count: usize,
    rule_ids: Vec<String>,
}

fn analyze_with_timeout(
    package_path: PathBuf,
    options: PackageAnalysisOptions,
    timeout_seconds: Option<u64>,
) -> anyhow::Result<CorpusSummary> {
    if let Some(timeout_seconds) = timeout_seconds {
        let (sender, receiver) = mpsc::channel();
        thread::spawn(move || {
            let summary = analyze_package_with_options(&package_path, options).map(|analysis| {
                let mut rules = BTreeSet::new();
                for finding in &analysis.findings {
                    rules.insert(finding.kind.rule_id().to_string());
                }
                CorpusSummary {
                    actual: if analysis.findings.is_empty() {
                        "clean".to_string()
                    } else {
                        "flagged".to_string()
                    },
                    finding_count: analysis.findings.len(),
                    rule_ids: rules.into_iter().collect(),
                }
            });
            let _ = sender.send(summary);
        });
        return match receiver.recv_timeout(Duration::from_secs(timeout_seconds)) {
            Ok(result) => result,
            Err(mpsc::RecvTimeoutError::Timeout) => Ok(CorpusSummary {
                actual: "manual-review".to_string(),
                finding_count: 0,
                rule_ids: vec![],
            }),
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                anyhow::bail!("analysis worker disconnected before returning a result")
            }
        };
    }

    let analysis = analyze_package_with_options(&package_path, options)?;
    let mut rules = BTreeSet::new();
    for finding in &analysis.findings {
        rules.insert(finding.kind.rule_id().to_string());
    }
    Ok(CorpusSummary {
        actual: if analysis.findings.is_empty() {
            "clean".to_string()
        } else {
            "flagged".to_string()
        },
        finding_count: analysis.findings.len(),
        rule_ids: rules.into_iter().collect(),
    })
}

fn checkout_repo(repo_dir: &Path, git: &str, rev: &str) -> anyhow::Result<()> {
    if !repo_dir.exists() {
        run_git(
            None,
            &["clone", "--no-checkout", git, repo_dir.to_str().unwrap()],
        )?;
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
        .map(|char| {
            if char.is_ascii_alphanumeric() {
                char
            } else {
                '_'
            }
        })
        .collect()
}

fn short_rev(rev: &str) -> &str {
    rev.get(..7).unwrap_or(rev)
}
