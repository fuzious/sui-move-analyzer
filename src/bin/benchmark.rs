use std::{
    path::PathBuf,
    time::Instant,
};
use sui_move_analyzer::security_analysis::{
    analyze_package_with_options, domain::RiskKind, PackageAnalysisOptions,
};


#[derive(Clone)]
struct CorpusEntry {
    path: &'static str,
    label: &'static str,
    expected_kind: Option<RiskKind>,
    min_expected: usize,
}

fn corpus() -> Vec<CorpusEntry> {
    vec![
        CorpusEntry {
            path: "tests/security_analysis/real_cases/cetus_vulnerable",
            label: "cetus_vulnerable",
            expected_kind: Some(RiskKind::FakeCheckedShift),
            min_expected: 1,
        },
        CorpusEntry {
            path: "tests/security_analysis/real_cases/cetus_patched",
            label: "cetus_patched",
            expected_kind: None,
            min_expected: 0,
        },
        CorpusEntry {
            path: "tests/security_analysis/real_cases/integer_mate_cloned_vulnerable",
            label: "integer_mate_cloned_vulnerable",
            expected_kind: Some(RiskKind::FakeCheckedShift),
            min_expected: 1,
        },
        CorpusEntry {
            path: "tests/security_analysis/real_cases/clmm_denominator_vulnerable",
            label: "clmm_denominator_vulnerable",
            expected_kind: Some(RiskKind::ReachableWeakDenominator),
            min_expected: 1,
        },
        CorpusEntry {
            path: "tests/security_analysis/real_cases/clmm_denominator_patched",
            label: "clmm_denominator_patched",
            expected_kind: None,
            min_expected: 0,
        },
        // ── Reduced / synthetic cases ────────────────────────────────────────
        CorpusEntry {
            path: "tests/security_analysis/reduced_cases/unsafe_direct",
            label: "unsafe_direct",
            expected_kind: Some(RiskKind::ReachableShiftTruncation),
            min_expected: 1,
        },
        CorpusEntry {
            path: "tests/security_analysis/reduced_cases/safe_guards",
            label: "safe_guards",
            expected_kind: None,
            min_expected: 0,
        },
        CorpusEntry {
            path: "tests/security_analysis/reduced_cases/helper_and_cast",
            label: "helper_and_cast",
            expected_kind: Some(RiskKind::FakeCheckedShift),
            min_expected: 1,
        },
        CorpusEntry {
            path: "tests/security_analysis/reduced_cases/invalid_shift",
            label: "invalid_shift",
            expected_kind: Some(RiskKind::InvalidShiftCount),
            min_expected: 1,
        },
        CorpusEntry {
            path: "tests/security_analysis/reduced_cases/lossy_right_shift",
            label: "lossy_right_shift",
            expected_kind: Some(RiskKind::ReachableLossyRightShift),
            min_expected: 1,
        },
        CorpusEntry {
            path: "tests/security_analysis/reduced_cases/safe_right_shift",
            label: "safe_right_shift",
            expected_kind: None,
            min_expected: 0,
        },
        CorpusEntry {
            path: "tests/security_analysis/reduced_cases/dynamic_u256_shift",
            label: "dynamic_u256_shift",
            expected_kind: None,
            min_expected: 0,
        },
        CorpusEntry {
            path: "tests/security_analysis/reduced_cases/neq_denominator_guard",
            label: "neq_denominator_guard",
            expected_kind: None,
            min_expected: 0,
        },
        CorpusEntry {
            path: "tests/security_analysis/reduced_cases/weak_denominator_warning",
            label: "weak_denominator_warning",
            expected_kind: Some(RiskKind::ReachableWeakDenominator),
            min_expected: 1,
        },
        CorpusEntry {
            path: "tests/security_analysis/reduced_cases/rounding_mismatch",
            label: "rounding_mismatch",
            expected_kind: Some(RiskKind::ReachableRoundingMismatch),
            min_expected: 1,
        },
        CorpusEntry {
            path: "tests/security_analysis/reduced_cases/masked_cast_safe",
            label: "masked_cast_safe",
            expected_kind: None,
            min_expected: 0,
        },
    ]
}

#[derive(Default)]
struct EntryResult {
    label: String,
    total_findings: usize,
    expected_kind: Option<RiskKind>,
    tp: usize,
    fp: usize,
    fn_count: usize,
    elapsed_ms: u128,
    error: Option<String>,
}

fn main() {
    let crate_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let entries = corpus();
    let mut results: Vec<EntryResult> = Vec::with_capacity(entries.len());

    let options = PackageAnalysisOptions::default();

    for entry in &entries {
        let pkg_path = crate_root.join(entry.path);
        let started = Instant::now();
        let analysis = analyze_package_with_options(&pkg_path, options.clone());
        let elapsed_ms = started.elapsed().as_millis();

        let mut r = EntryResult {
            label: entry.label.to_string(),
            expected_kind: entry.expected_kind.clone(),
            elapsed_ms,
            ..Default::default()
        };

        match analysis {
            Err(e) => {
                r.error = Some(e.to_string());
            }
            Ok(analysis) => {
                r.total_findings = analysis.findings.len();

                match &entry.expected_kind {
                    None => {
                        // Safe package — every finding is a false positive.
                        r.fp = analysis.findings.len();
                    }
                    Some(expected_kind) => {
                        // Vulnerable package.
                        let matching = analysis
                            .findings
                            .iter()
                            .filter(|f| f.kind == *expected_kind)
                            .count();
                        r.tp = matching;
                        r.fp = analysis
                            .findings
                            .iter()
                            .filter(|f| f.kind != *expected_kind)
                            .count();
                        if matching < entry.min_expected {
                            r.fn_count = entry.min_expected - matching;
                        }
                    }
                }
            }
        }
        results.push(r);
    }

    print_table(&results);

    let total_safe: usize = results
        .iter()
        .filter(|r| r.expected_kind.is_none() && r.error.is_none())
        .count();
    let total_vuln: usize = results
        .iter()
        .filter(|r| r.expected_kind.is_some() && r.error.is_none())
        .count();
    let total_fp: usize = results.iter().map(|r| r.fp).sum();
    let total_tp: usize = results.iter().map(|r| r.tp).sum();
    let total_fn: usize = results.iter().map(|r| r.fn_count).sum();
    let total_errors: usize = results.iter().filter(|r| r.error.is_some()).count();

    let fp_rate = if total_safe > 0 {
        // FP rate = packages with at least one FP / safe packages
        let safe_with_fp = results
            .iter()
            .filter(|r| r.expected_kind.is_none() && r.fp > 0)
            .count();
        safe_with_fp as f64 / total_safe as f64
    } else {
        0.0
    };

    let recall = if total_vuln > 0 {
        let detected = results
            .iter()
            .filter(|r| r.expected_kind.is_some() && r.tp > 0)
            .count();
        detected as f64 / total_vuln as f64
    } else {
        0.0
    };

    println!();
    println!("═══════════════════════════════════════════════════════");
    println!("  Corpus summary");
    println!("  Safe packages   : {total_safe}  (FP rate: {:.0}%)", fp_rate * 100.0);
    println!("  Vuln packages   : {total_vuln}  (recall: {:.0}%)", recall * 100.0);
    println!("  TP / FP / FN    : {total_tp} / {total_fp} / {total_fn}");
    if total_errors > 0 {
        println!("  Analysis errors : {total_errors}");
    }
    println!("═══════════════════════════════════════════════════════");

    // Non-zero exit if there are any false negatives or analysis errors.
    if total_fn > 0 || total_errors > 0 {
        std::process::exit(1);
    }
}

fn print_table(results: &[EntryResult]) {
    let col_label = 35usize;
    let col_findings = 8usize;
    let col_count = 4usize;
    println!(
        "\n{:<col_label$}  {:>col_findings$}  {:>col_count$}  {:>col_count$}  {:>col_count$}  {:>7}  {}",
        "package", "findings", "TP", "FP", "FN", "ms", "result"
    );
    println!("{}", "─".repeat(col_label + col_findings + col_count * 3 + 22));

    for r in results {
        if let Some(ref err) = r.error {
            println!(
                "{:<col_label$}  ERROR: {}",
                r.label,
                &err[..err.len().min(60)]
            );
            continue;
        }

        let verdict = if r.fn_count > 0 {
            "MISS"
        } else if r.fp > 0 {
            "FP"
        } else {
            "OK"
        };

        let expected_label = match &r.expected_kind {
            None => "0 (safe)".to_string(),
            Some(k) => format!("≥1 {:?}", k),
        };

        println!(
            "{:<col_label$}  {:>col_findings$}  {:>col_count$}  {:>col_count$}  {:>col_count$}  {:>7}  {} [{}]",
            r.label,
            r.total_findings,
            r.tp,
            r.fp,
            r.fn_count,
            r.elapsed_ms,
            verdict,
            expected_label,
        );
    }
}
