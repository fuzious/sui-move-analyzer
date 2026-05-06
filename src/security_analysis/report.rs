use crate::security_analysis::domain::RiskKind;
use move_compiler::{
    diag,
    diagnostics::{
        Diagnostic, Diagnostics,
        codes::{Severity, custom},
    },
};
use move_ir_types::location::Loc;
use std::collections::BTreeSet;

pub const SECURITY_PREFIX: &str = "Security ";
pub const SECURITY_CATEGORY: u8 = 98;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum SinkKind {
    PublicReturn,
    CallArgument,
    FieldWrite,
    ArithmeticUse,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SecurityFinding {
    pub key: String,
    pub kind: RiskKind,
    pub loc: Loc,
    pub sink_loc: Option<Loc>,
    pub helper_loc: Option<Loc>,
    pub severity: Severity,
    pub title: String,
    pub message: String,
    pub failed_condition: String,
    pub path_facts: Vec<String>,
    pub recommendation: String,
    pub sink_kind: SinkKind,
    pub sink_detail: Option<String>,
}

impl SecurityFinding {
    pub fn to_diagnostic(&self) -> Diagnostic {
        let (code, text) = match self.kind {
            RiskKind::ReachableShiftTruncation => (1, "reachable shift truncation"),
            RiskKind::FakeCheckedShift => (2, "fake checked shift helper"),
            RiskKind::ReachableNarrowCast => (3, "reachable narrowing cast"),
            RiskKind::InvalidShiftCount => (4, "invalid shift count"),
            RiskKind::ReachableLossyRightShift => (5, "reachable lossy right shift"),
            RiskKind::SuspiciousBitwiseArithmetic => (6, "suspicious bitwise arithmetic"),
            RiskKind::ReachableWeakDenominator => (7, "reachable weak denominator"),
            RiskKind::ReachableRoundingMismatch => (8, "reachable rounding mismatch"),
        };
        let diag_info = custom(
            SECURITY_PREFIX,
            self.severity,
            SECURITY_CATEGORY,
            code,
            text,
        );
        let mut diag = diag!(diag_info, (self.loc, self.title.clone()));
        if let Some(sink_loc) = self.sink_loc {
            diag.add_secondary_label((sink_loc, "value reaches a meaningful downstream sink"));
        }
        if let Some(helper_loc) = self.helper_loc {
            diag.add_secondary_label((helper_loc, "helper wrapper involved in this path"));
        }
        diag.add_note(self.message.clone());
        diag.add_note(format!("rule id: {}", self.kind.rule_id()));
        diag.add_note(format!("failed obligation: {}", self.failed_condition));
        if !self.path_facts.is_empty() {
            diag.add_note(format!("path facts: {}", self.path_facts.join(", ")));
        }
        if let Some(detail) = &self.sink_detail {
            diag.add_note(format!("sink detail: {detail}"));
        }
        diag.add_note(self.recommendation.clone());
        diag
    }
}

fn severity_rank(severity: Severity) -> u8 {
    match severity {
        Severity::Bug | Severity::BlockingError | Severity::NonblockingError => 3,
        Severity::Warning => 2,
        Severity::Note => 1,
    }
}

fn sink_kind_rank(kind: &SinkKind) -> u8 {
    match kind {
        SinkKind::CallArgument | SinkKind::FieldWrite => 2,
        SinkKind::PublicReturn => 1,
        SinkKind::ArithmeticUse => 0,
    }
}

pub fn normalize_findings(
    findings: impl IntoIterator<Item = SecurityFinding>,
) -> Vec<SecurityFinding> {
    let mut best_by_key = std::collections::BTreeMap::<String, SecurityFinding>::new();
    for finding in findings {
        match best_by_key.get(&finding.key) {
            Some(existing)
                if severity_rank(existing.severity) > severity_rank(finding.severity)
                    || (severity_rank(existing.severity) == severity_rank(finding.severity)
                        && sink_kind_rank(&existing.sink_kind)
                            >= sink_kind_rank(&finding.sink_kind)) => {}
            _ => {
                best_by_key.insert(finding.key.clone(), finding);
            }
        }
    }
    let findings = best_by_key.into_values().collect::<Vec<_>>();
    findings
        .iter()
        .filter(|finding| {
            if finding.kind != RiskKind::SuspiciousBitwiseArithmetic {
                return true;
            }
            !findings.iter().any(|other| {
                other.kind != RiskKind::SuspiciousBitwiseArithmetic
                    && severity_rank(other.severity) > severity_rank(finding.severity)
                    && other.sink_loc == finding.sink_loc
            })
        })
        .cloned()
        .collect()
}

pub fn collect_diagnostics(findings: impl IntoIterator<Item = SecurityFinding>) -> Diagnostics {
    let mut diags = Diagnostics::new();
    let mut seen = BTreeSet::new();
    for finding in normalize_findings(findings) {
        if seen.insert(finding.key.clone()) {
            diags.add(finding.to_diagnostic());
        }
    }
    diags
}
