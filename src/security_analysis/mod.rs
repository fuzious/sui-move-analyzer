pub mod cfg;
pub mod domain;
pub mod report;
pub mod rules;
pub mod sinks;
pub mod summaries;
pub mod transfer;

use anyhow::{Result, bail};
use move_compiler::{
    PASS_CFGIR, PASS_PARSER, PASS_TYPING,
    cfgir::ast as G,
    diagnostics::{Diagnostics, report_diagnostics_to_buffer},
    editions::Flavor,
    shared::files::MappedFiles,
};
use move_package::{
    BuildConfig,
    compilation::build_plan::BuildPlan,
    source_package::parsed_manifest::Dependencies,
};
use report::SecurityFinding;
use std::{io, path::Path};
use tempfile::tempdir;

pub fn analyze_cfgir_program(program: &G::Program) -> Diagnostics {
    transfer::ProgramAnalyzer::new(program).run()
}

pub fn analyze_cfgir_program_findings(program: &G::Program) -> Vec<SecurityFinding> {
    transfer::ProgramAnalyzer::new(program).run_findings()
}

pub struct PackageSecurityAnalysis {
    pub findings: Vec<SecurityFinding>,
    pub mapped_files: MappedFiles,
}

pub fn analyze_package(path: &Path, implicit_deps: Dependencies) -> Result<PackageSecurityAnalysis> {
    let install_dir = tempdir()?;
    let build_config = BuildConfig {
        test_mode: false,
        install_dir: Some(install_dir.path().to_path_buf()),
        default_flavor: Some(Flavor::Sui),
        skip_fetch_latest_git_deps: true,
        implicit_dependencies: implicit_deps,
        ..Default::default()
    };
    let resolution_graph = build_config.resolution_graph_for_package(path, None, &mut Vec::new())?;
    let build_plan = BuildPlan::create(&resolution_graph)?;
    let dependencies = build_plan.compute_dependencies();

    let mut findings: Option<Vec<SecurityFinding>> = None;
    let mut mapped_files: Option<MappedFiles> = None;

    build_plan.compile_with_driver_and_deps(dependencies, &mut io::sink(), |compiler| {
        let compiler = compiler.set_ide_mode();
        let (files, parse_result) = compiler.set_files_to_compile(None).run::<PASS_PARSER>()?;
        mapped_files = Some(files.clone());

        let compiler = match parse_result {
            Ok(compiler) => compiler,
            Err((_pass, diags)) => bail!(render_diags(&files, diags)),
        };

        let (compiler, parsed_program) = compiler.into_ast();
        let compiler = match compiler.at_parser(parsed_program).run::<PASS_TYPING>() {
            Ok(compiler) => compiler,
            Err((_pass, diags)) => bail!(render_diags(&files, diags)),
        };

        let (compiler, typed_program) = compiler.into_ast();
        let compiler = match compiler.at_typing(typed_program).run::<PASS_CFGIR>() {
            Ok(compiler) => compiler,
            Err((_pass, diags)) => bail!(render_diags(&files, diags)),
        };

        let (_compiler, cfgir_program) = compiler.into_ast();
        findings = Some(analyze_cfgir_program_findings(&cfgir_program));
        Ok((files, vec![]))
    })?;

    Ok(PackageSecurityAnalysis {
        findings: findings.unwrap_or_default(),
        mapped_files: mapped_files.expect("compiler should produce mapped files"),
    })
}

fn render_diags(files: &MappedFiles, diags: Diagnostics) -> String {
    String::from_utf8_lossy(&report_diagnostics_to_buffer(files, diags, false)).into_owned()
}

#[cfg(test)]
mod tests;
