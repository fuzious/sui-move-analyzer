pub mod cfg;
pub mod domain;
pub mod report;
pub mod rules;
pub mod sinks;
pub mod summaries;
pub mod transfer;

use crate::implicit_deps;
use anyhow::{Result, bail};
use move_compiler::{
    PASS_CFGIR, PASS_PARSER, PASS_TYPING,
    cfgir::ast as G,
    diagnostics::{Diagnostics, report_diagnostics_to_buffer},
    editions::Flavor,
    shared::files::MappedFiles,
};
use move_package::{
    BuildConfig, compilation::build_plan::BuildPlan, resolution::resolution_graph::ResolvedGraph,
    source_package::parsed_manifest::Dependencies,
};
use report::SecurityFinding;
use sha2::{Digest, Sha256};
use std::{
    fs, io,
    path::{Path, PathBuf},
    process::Command,
    time::{Duration, Instant},
};
use tempfile::tempdir;

pub fn analyze_cfgir_program(program: &G::Program) -> Diagnostics {
    transfer::ProgramAnalyzer::new(program, None, None, None, SecurityMathMode::Fast, 250).run()
}

pub fn analyze_cfgir_program_findings(program: &G::Program) -> Vec<SecurityFinding> {
    transfer::ProgramAnalyzer::new(program, None, None, None, SecurityMathMode::Fast, 250)
        .run_findings()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DependencyMode {
    Off,
    Auto,
    Forced,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AnalysisScope {
    RootOnly,
    RootAndDirectDeps,
    WholeGraph,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SecurityMathMode {
    Fast,
    Deep,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PackageSourceScope {
    RootPackage,
    DirectDependency,
    TransitiveDependency,
    Unknown,
}

impl PackageSourceScope {
    pub fn label(self) -> &'static str {
        match self {
            Self::RootPackage => "root",
            Self::DirectDependency => "direct-dependency",
            Self::TransitiveDependency => "transitive-dependency",
            Self::Unknown => "unknown",
        }
    }
}

#[derive(Clone, Debug)]
pub struct PackageAnalysisOptions {
    pub dependency_mode: DependencyMode,
    pub analysis_scope: AnalysisScope,
    pub reuse_build_cache: bool,
    pub security_math_mode: SecurityMathMode,
    pub security_smt_timeout_ms: u64,
}

impl Default for PackageAnalysisOptions {
    fn default() -> Self {
        Self {
            dependency_mode: DependencyMode::Auto,
            analysis_scope: AnalysisScope::RootAndDirectDeps,
            reuse_build_cache: true,
            security_math_mode: SecurityMathMode::Fast,
            security_smt_timeout_ms: 250,
        }
    }
}

#[derive(Clone, Debug)]
pub struct PackageScopeRoots {
    roots: Vec<(PathBuf, PackageSourceScope)>,
}

impl PackageScopeRoots {
    fn new(roots: Vec<(PathBuf, PackageSourceScope)>) -> Self {
        Self { roots }
    }

    fn scope_roots(&self, scope: AnalysisScope) -> Option<Vec<PathBuf>> {
        match scope {
            AnalysisScope::WholeGraph => None,
            AnalysisScope::RootOnly => Some(
                self.roots
                    .iter()
                    .filter(|(_, kind)| *kind == PackageSourceScope::RootPackage)
                    .map(|(path, _)| path.clone())
                    .collect(),
            ),
            AnalysisScope::RootAndDirectDeps => Some(
                self.roots
                    .iter()
                    .filter(|(_, kind)| {
                        matches!(
                            kind,
                            PackageSourceScope::RootPackage | PackageSourceScope::DirectDependency
                        )
                    })
                    .map(|(path, _)| path.clone())
                    .collect(),
            ),
        }
    }

    pub fn classify_path(&self, path: &Path) -> PackageSourceScope {
        let canonical = normalize_path(path);
        self.roots
            .iter()
            .filter(|(root, _)| canonical.starts_with(root))
            .max_by_key(|(root, _)| root.components().count())
            .map(|(_, scope)| *scope)
            .unwrap_or(PackageSourceScope::Unknown)
    }
}

pub struct PackageSecurityAnalysis {
    pub findings: Vec<SecurityFinding>,
    pub mapped_files: MappedFiles,
    pub install_dir: PathBuf,
    pub scope_roots: PackageScopeRoots,
    pub metrics: PackageAnalysisMetrics,
}

impl PackageSecurityAnalysis {
    pub fn finding_scope(&self, finding: &SecurityFinding) -> PackageSourceScope {
        let path = self.mapped_files.file_path(&finding.loc.file_hash());
        self.scope_roots.classify_path(path)
    }
}

#[derive(Clone, Debug, Default)]
pub struct PackageAnalysisMetrics {
    pub resolution: Duration,
    pub parse: Duration,
    pub typing: Duration,
    pub cfgir: Duration,
    pub finding_pass: Duration,
    pub total: Duration,
}

pub fn analyze_package(
    path: &Path,
    implicit_deps: Dependencies,
) -> Result<PackageSecurityAnalysis> {
    let options = PackageAnalysisOptions {
        dependency_mode: if implicit_deps.is_empty() {
            DependencyMode::Off
        } else {
            DependencyMode::Forced
        },
        analysis_scope: AnalysisScope::WholeGraph,
        reuse_build_cache: false,
        security_math_mode: SecurityMathMode::Fast,
        security_smt_timeout_ms: 250,
    };
    analyze_package_inner(path, options, implicit_deps)
}

pub fn analyze_package_with_options(
    path: &Path,
    options: PackageAnalysisOptions,
) -> Result<PackageSecurityAnalysis> {
    match options.dependency_mode {
        DependencyMode::Off => analyze_package_inner(path, options, Default::default()),
        DependencyMode::Forced => analyze_package_inner(path, options, implicit_deps()),
        DependencyMode::Auto => {
            match analyze_package_inner(path, options.clone(), Default::default()) {
                Ok(analysis) => Ok(analysis),
                Err(first_error) => {
                    if should_retry_with_implicit_deps(&first_error.to_string()) {
                        analyze_package_inner(path, options, implicit_deps()).or(Err(first_error))
                    } else {
                        Err(first_error)
                    }
                }
            }
        }
    }
}

fn render_diags(files: &MappedFiles, diags: Diagnostics) -> String {
    String::from_utf8_lossy(&report_diagnostics_to_buffer(files, diags, false)).into_owned()
}

fn analyze_package_inner(
    path: &Path,
    options: PackageAnalysisOptions,
    implicit_dependencies: Dependencies,
) -> Result<PackageSecurityAnalysis> {
    let temp_install_dir = if options.reuse_build_cache {
        None
    } else {
        Some(tempdir()?)
    };
    let install_dir = match &temp_install_dir {
        Some(temp) => temp.path().to_path_buf(),
        None => persistent_install_dir(path)?,
    };
    fs::create_dir_all(&install_dir)?;

    let build_config = BuildConfig {
        test_mode: false,
        install_dir: Some(install_dir.clone()),
        default_flavor: Some(Flavor::Sui),
        skip_fetch_latest_git_deps: true,
        implicit_dependencies,
        ..Default::default()
    };
    let mut metrics = PackageAnalysisMetrics::default();
    let started_total = Instant::now();
    let started_resolution = Instant::now();
    let resolution_graph =
        build_config.resolution_graph_for_package(path, None, &mut Vec::new())?;
    metrics.resolution = started_resolution.elapsed();
    let scope_roots = scope_roots_from_graph(&resolution_graph);
    let allowed_roots = scope_roots.scope_roots(options.analysis_scope);
    let root_roots = scope_roots.scope_roots(AnalysisScope::RootOnly);
    let build_plan = BuildPlan::create(&resolution_graph)?;
    let dependencies = build_plan.compute_dependencies();

    let mut findings: Option<Vec<SecurityFinding>> = None;
    let mut mapped_files: Option<MappedFiles> = None;

    build_plan.compile_with_driver_and_deps(dependencies, &mut io::sink(), |compiler| {
        let compiler = compiler.set_ide_mode();
        let started_parse = Instant::now();
        let (files, parse_result) = compiler.set_files_to_compile(None).run::<PASS_PARSER>()?;
        metrics.parse = started_parse.elapsed();
        mapped_files = Some(files.clone());

        let compiler = match parse_result {
            Ok(compiler) => compiler,
            Err((_pass, diags)) => bail!(render_diags(&files, diags)),
        };

        let (compiler, parsed_program) = compiler.into_ast();
        let started_typing = Instant::now();
        let compiler = match compiler.at_parser(parsed_program).run::<PASS_TYPING>() {
            Ok(compiler) => compiler,
            Err((_pass, diags)) => bail!(render_diags(&files, diags)),
        };
        metrics.typing = started_typing.elapsed();

        let (compiler, typed_program) = compiler.into_ast();
        let started_cfgir = Instant::now();
        let compiler = match compiler.at_typing(typed_program).run::<PASS_CFGIR>() {
            Ok(compiler) => compiler,
            Err((_pass, diags)) => bail!(render_diags(&files, diags)),
        };
        metrics.cfgir = started_cfgir.elapsed();

        let (_compiler, cfgir_program) = compiler.into_ast();
        let started_findings = Instant::now();
        findings = Some(
            transfer::ProgramAnalyzer::new(
                &cfgir_program,
                Some(&files),
                allowed_roots.as_deref(),
                root_roots.as_deref(),
                options.security_math_mode,
                options.security_smt_timeout_ms,
            )
            .run_findings(),
        );
        metrics.finding_pass = started_findings.elapsed();
        Ok((files, vec![]))
    })?;
    metrics.total = started_total.elapsed();

    Ok(PackageSecurityAnalysis {
        findings: findings.unwrap_or_default(),
        mapped_files: mapped_files.expect("compiler should produce mapped files"),
        install_dir,
        scope_roots,
        metrics,
    })
}

fn scope_roots_from_graph(resolution_graph: &ResolvedGraph) -> PackageScopeRoots {
    let root_name = resolution_graph.root_package();
    let root_package = resolution_graph
        .package_table
        .get(&root_name)
        .expect("root package should exist");
    let direct_deps = root_package.immediate_dependencies(resolution_graph);

    let mut roots = vec![(
        normalize_path(&root_package.package_path),
        PackageSourceScope::RootPackage,
    )];
    for (name, package) in &resolution_graph.package_table {
        if *name == root_name {
            continue;
        }
        let scope = if direct_deps.contains(name) {
            PackageSourceScope::DirectDependency
        } else {
            PackageSourceScope::TransitiveDependency
        };
        roots.push((normalize_path(&package.package_path), scope));
    }
    PackageScopeRoots::new(roots)
}

fn normalize_path(path: &Path) -> PathBuf {
    dunce::canonicalize(path).unwrap_or_else(|_| path.to_path_buf())
}

fn persistent_install_dir(path: &Path) -> Result<PathBuf> {
    let cache_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("security_analysis");
    fs::create_dir_all(&cache_root)?;
    Ok(cache_root.join(cache_key(path)))
}

fn cache_key(path: &Path) -> String {
    let canonical = normalize_path(path);
    let mut hasher = Sha256::new();
    hasher.update(canonical.to_string_lossy().as_bytes());
    if let Some(revision) = git_revisionish(&canonical) {
        hasher.update(revision.as_bytes());
    } else {
        hasher.update(read_manifest_fingerprint(&canonical).as_bytes());
    }
    format!("{:x}", hasher.finalize())
}

fn read_manifest_fingerprint(path: &Path) -> String {
    fs::read_to_string(path.join("Move.toml")).unwrap_or_default()
}

fn git_revisionish(path: &Path) -> Option<String> {
    let output = Command::new("git")
        .arg("-C")
        .arg(path)
        .arg("rev-parse")
        .arg("HEAD")
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let revision = String::from_utf8(output.stdout).ok()?;
    Some(revision.trim().to_string())
}

pub(crate) fn should_retry_with_implicit_deps(error_text: &str) -> bool {
    let lower = error_text.to_ascii_lowercase();
    let missing_std_or_sui_address = (lower.contains("address 'std'")
        || lower.contains("address 'sui'"))
        && (lower.contains("not assigned") || lower.contains("unresolved addresses"));
    let missing_framework_module =
        lower.contains("unbound module") && (lower.contains("std::") || lower.contains("sui::"));
    missing_std_or_sui_address || missing_framework_module
}

#[cfg(test)]
mod tests;
