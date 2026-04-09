use super::{
    AnalysisScope, DependencyMode, PackageAnalysisOptions, PackageSecurityAnalysis,
    PackageSourceScope, SecurityMathMode, analyze_package, analyze_package_with_options,
    domain::RiskKind,
    report::SecurityFinding, should_retry_with_implicit_deps,
};
use anyhow::{Context, Result};
use move_compiler::diagnostics::codes::Severity;
use std::path::PathBuf;

impl PackageSecurityAnalysis {
    fn find_by_rule(&self, rule: RiskKind) -> Vec<&SecurityFinding> {
        self.findings
            .iter()
            .filter(|finding| finding.kind == rule)
            .collect()
    }

    fn find_in_file(&self, rule: RiskKind, file_suffix: &str) -> Vec<&SecurityFinding> {
        self.findings
            .iter()
            .filter(|finding| finding.kind == rule)
            .filter(|finding| self.path_for(finding).ends_with(file_suffix))
            .collect()
    }

    fn path_for(&self, finding: &SecurityFinding) -> String {
        self.mapped_files
            .file_path(&finding.loc.file_hash())
            .display()
            .to_string()
    }

    fn line_for(&self, finding: &SecurityFinding) -> usize {
        self.mapped_files
            .start_position_opt(&finding.loc)
            .expect("finding should map to a source location")
            .line_offset()
            + 1
    }
}

fn analyze_fixture(relative_path: &str) -> Result<PackageSecurityAnalysis> {
    let package_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(relative_path);
    analyze_package(&package_path, Default::default())
        .with_context(|| format!("failed to analyze fixture {}", package_path.display()))
}

fn analyze_fixture_with_options(
    relative_path: &str,
    options: PackageAnalysisOptions,
) -> Result<PackageSecurityAnalysis> {
    let package_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(relative_path);
    analyze_package_with_options(&package_path, options)
        .with_context(|| format!("failed to analyze fixture {}", package_path.display()))
}

#[test]
fn cetus_vulnerable_helper_path_is_reported() -> Result<()> {
    let analysis = analyze_fixture("tests/security_analysis/real_cases/cetus_vulnerable")?;
    let findings = analysis.find_in_file(RiskKind::FakeCheckedShift, "math_u256.move");
    assert!(
        !findings.is_empty(),
        "expected fake checked shift finding, got {:?}",
        analysis.findings
    );

    let finding = findings[0];
    assert_eq!(finding.severity, Severity::NonblockingError);
    assert_eq!(analysis.line_for(finding), 7);
    assert!(finding.failed_condition.contains("MAX_U256 >> 64"));
    assert!(
        finding
            .message
            .contains("weaker than the true no-truncation bound")
    );
    assert!(finding.title.contains("checked-shift helper"));
    Ok(())
}

#[test]
fn cloned_integer_mate_helper_is_reported() -> Result<()> {
    let analysis =
        analyze_fixture("tests/security_analysis/real_cases/integer_mate_cloned_vulnerable")?;
    let findings = analysis.find_in_file(RiskKind::FakeCheckedShift, "math_u256.move");
    assert!(
        !findings.is_empty(),
        "expected vulnerable cloned helper finding, got {:?}",
        analysis.findings
    );
    let finding = findings[0];
    assert_eq!(analysis.line_for(finding), 23);
    assert!(finding.failed_condition.contains("MAX_U256 >> 64"));
    assert!(
        finding
            .message
            .contains("weaker than the true no-truncation bound")
    );
    Ok(())
}

#[test]
fn cetus_patched_helper_is_suppressed() -> Result<()> {
    let analysis = analyze_fixture("tests/security_analysis/real_cases/cetus_patched")?;
    assert!(
        analysis.find_by_rule(RiskKind::FakeCheckedShift).is_empty(),
        "patched helper should not be reported: {:?}",
        analysis.findings
    );
    assert!(
        analysis
            .find_by_rule(RiskKind::ReachableShiftTruncation)
            .is_empty(),
        "patched helper should not leave a shift-truncation finding: {:?}",
        analysis.findings
    );
    Ok(())
}

#[test]
fn clmm_denominator_zero_path_is_reported() -> Result<()> {
    let analysis =
        analyze_fixture("tests/security_analysis/real_cases/clmm_denominator_vulnerable")?;
    let findings = analysis.find_in_file(RiskKind::ReachableWeakDenominator, "clmm_math.move");
    assert!(
        !findings.is_empty(),
        "unexpected findings: {:?}",
        analysis.findings
    );
    let finding = findings[0];
    assert_eq!(finding.severity, Severity::NonblockingError);
    assert!(finding.title.contains("Denominator may be zero"));
    assert!(finding.failed_condition.contains("!= 0"));
    Ok(())
}

#[test]
fn clmm_denominator_with_explicit_price_guards_is_suppressed() -> Result<()> {
    let analysis = analyze_fixture("tests/security_analysis/real_cases/clmm_denominator_patched")?;
    assert!(
        analysis
            .find_by_rule(RiskKind::ReachableWeakDenominator)
            .is_empty(),
        "patched denominator guards should suppress findings: {:?}",
        analysis.findings
    );
    Ok(())
}

#[test]
fn neq_denominator_guard_suppresses_division_warning() -> Result<()> {
    let analysis = analyze_fixture("tests/security_analysis/reduced_cases/neq_denominator_guard")?;
    assert!(
        analysis
            .find_by_rule(RiskKind::ReachableWeakDenominator)
            .is_empty(),
        "x != 0 guards should suppress denominator findings: {:?}",
        analysis.findings
    );
    Ok(())
}

#[test]
fn safe_exact_bound_direct_shift_is_suppressed() -> Result<()> {
    let analysis = analyze_fixture("tests/security_analysis/reduced_cases/safe_guards")?;
    assert!(
        analysis.findings.is_empty(),
        "guarded exact-bound shift should be safe: {:?}",
        analysis.findings
    );
    Ok(())
}

#[test]
fn assert_narrowing_suppresses_shift_warning() -> Result<()> {
    let analysis = analyze_fixture("tests/security_analysis/reduced_cases/safe_guards")?;
    assert!(
        analysis.findings.is_empty(),
        "assert! should narrow the path enough to suppress the shift: {:?}",
        analysis.findings
    );
    Ok(())
}

#[test]
fn unsafe_direct_shift_is_reported() -> Result<()> {
    let analysis = analyze_fixture("tests/security_analysis/reduced_cases/unsafe_direct")?;
    let findings = analysis.find_in_file(RiskKind::ReachableShiftTruncation, "unsafe_direct.move");
    assert_eq!(
        findings.len(),
        1,
        "unexpected findings: {:?}",
        analysis.findings
    );
    let finding = findings[0];
    assert!(matches!(
        finding.severity,
        Severity::Warning | Severity::NonblockingError
    ));
    assert_eq!(analysis.line_for(finding), 3);
    assert!(finding.failed_condition.contains("MAX_U256 >> 64"));
    Ok(())
}

#[test]
fn wrong_helper_wrapper_is_reported() -> Result<()> {
    let analysis = analyze_fixture("tests/security_analysis/reduced_cases/helper_and_cast")?;
    let findings = analysis.find_in_file(RiskKind::FakeCheckedShift, "helper_and_cast.move");
    assert!(
        !findings.is_empty(),
        "expected unsound checked helper finding: {:?}",
        analysis.findings
    );
    let finding = findings[0];
    assert!(matches!(
        finding.severity,
        Severity::Warning | Severity::NonblockingError
    ));
    assert!(finding.failed_condition.contains("MAX_U256 >> 64"));
    Ok(())
}

#[test]
fn invalid_shift_count_is_reported_separately() -> Result<()> {
    let analysis = analyze_fixture("tests/security_analysis/reduced_cases/invalid_shift")?;
    let findings = analysis.find_in_file(RiskKind::InvalidShiftCount, "invalid_shift.move");
    assert_eq!(
        findings.len(),
        1,
        "unexpected findings: {:?}",
        analysis.findings
    );
    let finding = findings[0];
    assert_eq!(analysis.line_for(finding), 3);
    assert!(finding.failed_condition.contains("64 < 64"));
    Ok(())
}

#[test]
fn cast_after_shift_is_reported() -> Result<()> {
    let analysis = analyze_fixture("tests/security_analysis/reduced_cases/helper_and_cast")?;
    let findings = analysis.find_in_file(RiskKind::ReachableNarrowCast, "helper_and_cast.move");
    assert!(
        !findings.is_empty(),
        "expected reachable narrowing cast finding: {:?}",
        analysis.findings
    );
    let finding = findings
        .iter()
        .find(|finding| analysis.line_for(finding) == 18)
        .copied()
        .unwrap_or(findings[0]);
    assert!(matches!(
        finding.severity,
        Severity::Warning | Severity::NonblockingError
    ));
    assert!(finding.failed_condition.contains("<="));
    Ok(())
}

#[test]
fn lossy_right_shift_into_amount_sink_is_reported() -> Result<()> {
    let analysis = analyze_fixture("tests/security_analysis/reduced_cases/lossy_right_shift")?;
    let findings =
        analysis.find_in_file(RiskKind::ReachableLossyRightShift, "lossy_right_shift.move");
    assert_eq!(
        findings.len(),
        1,
        "unexpected findings: {:?}",
        analysis.findings
    );
    let finding = findings[0];
    assert!(matches!(
        finding.severity,
        Severity::Warning | Severity::NonblockingError
    ));
    assert_eq!(analysis.line_for(finding), 3);
    assert!(finding.failed_condition.contains("&"));
    Ok(())
}

#[test]
fn exact_right_shift_after_mask_is_suppressed() -> Result<()> {
    let analysis = analyze_fixture("tests/security_analysis/reduced_cases/safe_right_shift")?;
    assert!(
        analysis.findings.is_empty(),
        "masked exact right shift should be safe: {:?}",
        analysis.findings
    );
    Ok(())
}

#[test]
fn dynamic_u256_shift_does_not_warn_without_a_real_obligation() -> Result<()> {
    let analysis = analyze_fixture("tests/security_analysis/reduced_cases/dynamic_u256_shift")?;
    assert!(
        analysis.findings.is_empty(),
        "dynamic u256 shifts with a u8 shift amount should not warn on their own: {:?}",
        analysis.findings
    );
    Ok(())
}

#[test]
fn masked_bit_extract_before_cast_is_suppressed() -> Result<()> {
    let analysis = analyze_fixture("tests/security_analysis/reduced_cases/masked_cast_safe")?;
    assert!(
        analysis.findings.is_empty(),
        "masking to the destination range should suppress cast findings: {:?}",
        analysis.findings
    );
    Ok(())
}

#[test]
fn bitwise_or_and_xor_before_amount_math_warn() -> Result<()> {
    let analysis = analyze_fixture("tests/security_analysis/reduced_cases/bitwise_warning")?;
    let findings = analysis.find_in_file(
        RiskKind::SuspiciousBitwiseArithmetic,
        "bitwise_warning.move",
    );
    assert_eq!(
        findings.len(),
        2,
        "unexpected findings: {:?}",
        analysis.findings
    );
    for finding in findings {
        assert_eq!(finding.severity, Severity::Warning);
    }
    Ok(())
}

#[test]
fn weak_denominator_product_only_guarded_at_product_level_warns() -> Result<()> {
    let analysis =
        analyze_fixture("tests/security_analysis/reduced_cases/weak_denominator_warning")?;
    let findings = analysis.find_in_file(
        RiskKind::ReachableWeakDenominator,
        "weak_denominator_warning.move",
    );
    assert_eq!(
        findings.len(),
        1,
        "unexpected findings: {:?}",
        analysis.findings
    );
    let finding = findings[0];
    assert_eq!(finding.severity, Severity::Warning);
    assert!(finding.title.contains("Independent denominator factors"));
    Ok(())
}

#[test]
fn denominator_obligation_survives_symbol_renames() -> Result<()> {
    let analysis = analyze_fixture("tests/security_analysis/reduced_cases/semantic_rename")?;
    let findings =
        analysis.find_in_file(RiskKind::ReachableWeakDenominator, "semantic_rename.move");
    assert!(
        !findings.is_empty(),
        "expected semantic denominator obligation finding after symbol renames: {:?}",
        analysis.findings
    );
    assert!(
        findings.iter().any(|finding| finding
            .message
            .contains("independent denominator factor")),
        "expected independent-factor obligation evidence: {:?}",
        findings
    );
    Ok(())
}

#[test]
fn mixed_rounding_paths_report_rounding_mismatch() -> Result<()> {
    let analysis = analyze_fixture("tests/security_analysis/reduced_cases/rounding_mismatch")?;
    let findings =
        analysis.find_in_file(RiskKind::ReachableRoundingMismatch, "rounding_mismatch.move");
    assert!(
        !findings.is_empty(),
        "expected mixed-rounding mismatch finding, got {:?}",
        analysis.findings
    );
    assert!(
        findings
            .iter()
            .any(|finding| finding.message.contains("rounding mode")),
        "expected rounding evidence in mismatch finding message: {:?}",
        findings
    );
    Ok(())
}

#[test]
fn safe_or_guard_checked_helper_is_suppressed() -> Result<()> {
    let analysis =
        analyze_fixture("tests/security_analysis/reduced_cases/safe_disjunctive_helper")?;
    assert!(
        analysis.findings.is_empty(),
        "safe disjunctive helper guard should suppress findings: {:?}",
        analysis.findings
    );
    Ok(())
}

#[test]
fn helper_return_unrelated_param_reports_seed_shift() -> Result<()> {
    let analysis = analyze_fixture("tests/security_analysis/reduced_cases/reference_regressions")?;
    let findings = analysis.find_in_file(
        RiskKind::ReachableShiftTruncation,
        "reference_regressions.move",
    );
    assert_eq!(
        findings.len(),
        1,
        "unexpected findings: {:?}",
        analysis.findings
    );
    let finding = findings[0];
    assert!(finding.message.contains("seed"));
    assert!(!finding.message.contains("coupon"));
    Ok(())
}

#[test]
fn weak_sink_is_lower_severity_than_cetus_path() -> Result<()> {
    let cetus = analyze_fixture("tests/security_analysis/real_cases/cetus_vulnerable")?;
    let weak = analyze_fixture("tests/security_analysis/sink_cases/weak_sink")?;

    let cetus_finding = cetus
        .find_in_file(RiskKind::FakeCheckedShift, "math_u256.move")
        .into_iter()
        .next()
        .context("missing Cetus helper finding")?;
    let weak_finding = weak
        .find_in_file(RiskKind::ReachableShiftTruncation, "weak_sink.move")
        .into_iter()
        .next()
        .context("missing weak sink shift finding")?;

    assert_eq!(cetus_finding.severity, Severity::NonblockingError);
    assert_eq!(weak_finding.severity, Severity::Warning);
    Ok(())
}

#[test]
fn package_with_local_dependency_is_analyzed() -> Result<()> {
    let analysis =
        analyze_fixture("tests/security_analysis/dependency_cases/local_dependency_root")?;
    assert!(
        analysis.findings.is_empty(),
        "dependency smoke fixture should compile cleanly once the local dependency resolves: {:?}",
        analysis.findings
    );
    Ok(())
}

#[test]
fn root_only_scope_excludes_dependency_findings() -> Result<()> {
    let analysis = analyze_fixture_with_options(
        "tests/security_analysis/dependency_cases/scope_root",
        PackageAnalysisOptions {
            dependency_mode: DependencyMode::Off,
            analysis_scope: AnalysisScope::RootOnly,
            reuse_build_cache: false,
            security_math_mode: SecurityMathMode::Fast,
            security_smt_timeout_ms: 250,
        },
    )?;
    assert!(
        analysis.findings.is_empty(),
        "root-only analysis should ignore dependency-owned findings: {:?}",
        analysis.findings
    );
    Ok(())
}

#[test]
fn root_and_direct_scope_includes_direct_dependency_findings_only() -> Result<()> {
    let analysis = analyze_fixture_with_options(
        "tests/security_analysis/dependency_cases/scope_root",
        PackageAnalysisOptions {
            dependency_mode: DependencyMode::Off,
            analysis_scope: AnalysisScope::RootAndDirectDeps,
            reuse_build_cache: false,
            security_math_mode: SecurityMathMode::Fast,
            security_smt_timeout_ms: 250,
        },
    )?;
    let direct_findings = analysis.find_in_file(
        RiskKind::ReachableShiftTruncation,
        "scope_direct/sources/direct_risk.move",
    );
    assert_eq!(
        direct_findings.len(),
        1,
        "unexpected findings: {:?}",
        analysis.findings
    );
    assert!(
        analysis
            .find_in_file(
                RiskKind::ReachableShiftTruncation,
                "scope_transitive/sources/transitive_risk.move",
            )
            .is_empty(),
        "transitive findings should be out of scope: {:?}",
        analysis.findings
    );
    assert_eq!(
        analysis.finding_scope(direct_findings[0]),
        PackageSourceScope::DirectDependency
    );
    Ok(())
}

#[test]
fn whole_graph_scope_includes_transitive_dependency_findings() -> Result<()> {
    let analysis = analyze_fixture_with_options(
        "tests/security_analysis/dependency_cases/scope_root",
        PackageAnalysisOptions {
            dependency_mode: DependencyMode::Off,
            analysis_scope: AnalysisScope::WholeGraph,
            reuse_build_cache: false,
            security_math_mode: SecurityMathMode::Fast,
            security_smt_timeout_ms: 250,
        },
    )?;
    assert_eq!(
        analysis
            .find_in_file(
                RiskKind::ReachableShiftTruncation,
                "scope_direct/sources/direct_risk.move",
            )
            .len(),
        1,
        "expected direct dependency finding: {:?}",
        analysis.findings
    );
    let transitive = analysis.find_in_file(
        RiskKind::ReachableShiftTruncation,
        "scope_transitive/sources/transitive_risk.move",
    );
    assert_eq!(
        transitive.len(),
        1,
        "expected transitive finding: {:?}",
        analysis.findings
    );
    assert_eq!(
        analysis.finding_scope(transitive[0]),
        PackageSourceScope::TransitiveDependency
    );
    Ok(())
}

#[test]
fn package_cache_dir_is_reused_when_enabled() -> Result<()> {
    let options = PackageAnalysisOptions {
        dependency_mode: DependencyMode::Off,
        analysis_scope: AnalysisScope::WholeGraph,
        reuse_build_cache: true,
        security_math_mode: SecurityMathMode::Fast,
        security_smt_timeout_ms: 250,
    };
    let first = analyze_fixture_with_options(
        "tests/security_analysis/dependency_cases/local_dependency_root",
        options.clone(),
    )?;
    let second = analyze_fixture_with_options(
        "tests/security_analysis/dependency_cases/local_dependency_root",
        options,
    )?;
    assert_eq!(
        first.install_dir, second.install_dir,
        "persistent cache should reuse the same install dir"
    );
    Ok(())
}

#[test]
fn missing_framework_errors_trigger_auto_retry_detector() {
    assert!(should_retry_with_implicit_deps(
        "address 'std' is not assigned a value and unbound module 'sui::coin'"
    ));
    assert!(should_retry_with_implicit_deps(
        "Unresolved addresses: [Named address 'sui' in package 'Demo']"
    ));
}

#[test]
fn unrelated_dependency_errors_do_not_trigger_auto_retry_detector() {
    assert!(!should_retry_with_implicit_deps(
        "Unbound module 'local_math::helper' in root::entry"
    ));
    assert!(!should_retry_with_implicit_deps("Compilation error"));
}

#[test]
fn missing_local_dependency_fails_fast() -> Result<()> {
    let package_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/security_analysis/dependency_cases/missing_local_dependency_root");

    let err = match analyze_package(&package_path, Default::default()) {
        Ok(analysis) => panic!(
            "fixture should fail without declared dependency, got {:?}",
            analysis.findings
        ),
        Err(err) => err,
    };
    let err_text = err.to_string();
    assert!(
        err_text.contains("local_math::helper") || err_text.contains("Unbound module"),
        "unexpected error without declared dependency: {err_text}"
    );
    Ok(())
}
