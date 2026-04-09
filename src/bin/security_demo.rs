use clap::{Parser, ValueEnum};
use std::{path::PathBuf, time::Instant};
use sui_move_analyzer::{
    discover_manifest_and_kind,
    security_analysis::{
        AnalysisScope, DependencyMode, PackageAnalysisOptions, SecurityMathMode,
        analyze_package_with_options,
    },
};

#[derive(Parser, Debug)]
#[command(
    author,
    version,
    about = "Run the Sui Move security shift analysis demo"
)]
struct Options {
    /// Path to a Move package directory or any .move file inside it
    path: PathBuf,

    /// Analysis scope: root package only, root plus direct dependencies, or the whole graph
    #[arg(long, value_enum, default_value_t = ScopeArg::Direct)]
    scope: ScopeArg,

    /// Framework dependency resolution mode
    #[arg(long, value_enum, default_value_t = DependencyModeArg::Auto)]
    dependency_mode: DependencyModeArg,

    /// Security math analysis mode: fast abstract mode or deep mode with extra obligation reasoning
    #[arg(long = "security-math-mode", value_enum, default_value_t = MathModeArg::Fast)]
    security_math_mode: MathModeArg,

    /// Timeout budget in milliseconds for deep-mode obligation checks
    #[arg(long = "security-smt-timeout-ms", default_value_t = 250)]
    security_smt_timeout_ms: u64,
}

#[derive(Clone, Copy, Debug, ValueEnum)]
enum ScopeArg {
    Root,
    Direct,
    All,
}

#[derive(Clone, Copy, Debug, ValueEnum)]
enum DependencyModeArg {
    Off,
    Auto,
    Forced,
}

#[derive(Clone, Copy, Debug, ValueEnum)]
enum MathModeArg {
    Fast,
    Deep,
}

fn main() -> anyhow::Result<()> {
    let options = Options::parse();
    let package_path = package_root(&options.path)?;
    let started = Instant::now();
    let analysis = analyze_package_with_options(
        &package_path,
        PackageAnalysisOptions {
            dependency_mode: match options.dependency_mode {
                DependencyModeArg::Off => DependencyMode::Off,
                DependencyModeArg::Auto => DependencyMode::Auto,
                DependencyModeArg::Forced => DependencyMode::Forced,
            },
            analysis_scope: match options.scope {
                ScopeArg::Root => AnalysisScope::RootOnly,
                ScopeArg::Direct => AnalysisScope::RootAndDirectDeps,
                ScopeArg::All => AnalysisScope::WholeGraph,
            },
            reuse_build_cache: true,
            security_math_mode: match options.security_math_mode {
                MathModeArg::Fast => SecurityMathMode::Fast,
                MathModeArg::Deep => SecurityMathMode::Deep,
            },
            security_smt_timeout_ms: options.security_smt_timeout_ms,
        },
    )?;
    eprintln!(
        "[security_demo] analyzed {} in {:.2?} using {} scope / {} deps / {} math mode",
        package_path.display(),
        started.elapsed(),
        analysis_scope_label(options.scope),
        dependency_mode_label(options.dependency_mode),
        math_mode_label(options.security_math_mode),
    );
    eprintln!(
        "[security_demo] phases: resolution={:.2?} parse={:.2?} typing={:.2?} cfgir={:.2?} findings={:.2?} total={:.2?}",
        analysis.metrics.resolution,
        analysis.metrics.parse,
        analysis.metrics.typing,
        analysis.metrics.cfgir,
        analysis.metrics.finding_pass,
        analysis.metrics.total,
    );

    if analysis.findings.is_empty() {
        println!("No security findings for {}", package_path.display());
        return Ok(());
    }

    println!("file | line | scope | severity | rule | message");
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
                analysis.finding_scope(finding).label().to_string(),
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
            .then(left.4.cmp(right.4))
    });

    for (file, line, scope, severity, rule, message) in rows {
        println!("{file} | {line} | {scope} | {severity} | {rule} | {message}");
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

fn analysis_scope_label(scope: ScopeArg) -> &'static str {
    match scope {
        ScopeArg::Root => "root",
        ScopeArg::Direct => "direct",
        ScopeArg::All => "all",
    }
}

fn dependency_mode_label(mode: DependencyModeArg) -> &'static str {
    match mode {
        DependencyModeArg::Off => "off",
        DependencyModeArg::Auto => "auto",
        DependencyModeArg::Forced => "forced",
    }
}

fn math_mode_label(mode: MathModeArg) -> &'static str {
    match mode {
        MathModeArg::Fast => "fast",
        MathModeArg::Deep => "deep",
    }
}
