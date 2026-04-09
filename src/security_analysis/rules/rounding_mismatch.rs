use super::{RuleCtx, single_param_index};
use crate::security_analysis::domain::{
    ObligationKind, ProofMode, RiskKind, RiskOrigin, ValueState,
};
use move_ir_types::location::Loc;

/// Check whether a value whose formula facts carry an unresolved rounding
/// conflict reaches a sink.
///
/// `sink_loc` is the location where the value is consumed; `sink_detail` is
/// human-readable evidence for the sink.
///
/// Returns `None` when there is no rounding conflict or the formula context is
/// empty.
pub fn check(
    ctx: &RuleCtx,
    value: &ValueState,
    sink_loc: Loc,
    sink_detail: Option<&str>,
) -> Option<RiskOrigin> {
    let facts = value.formula_facts.as_ref()?;
    if !facts.rounding_conflict {
        return None;
    }
    if facts.factors.is_empty() && facts.root_expr.is_none() {
        return None;
    }

    let root_id = facts
        .root_expr
        .as_ref()
        .map(|root| root.id)
        .unwrap_or_default();

    let rounding_trace = if facts.rounding_trace.is_empty() {
        String::new()
    } else {
        format!(" rounding trace: {}", facts.rounding_trace.join(" -> "))
    };

    let expr_text = match sink_detail {
        Some(detail) => {
            if rounding_trace.is_empty() {
                detail.to_string()
            } else {
                format!("{detail};{rounding_trace}")
            }
        }
        None => {
            if rounding_trace.is_empty() {
                "value".to_string()
            } else {
                rounding_trace.trim_start().to_string()
            }
        }
    };

    let key = format!(
        "{}:{}:{}:{}",
        RiskKind::ReachableRoundingMismatch.rule_id(),
        sink_loc.file_hash(),
        sink_loc.start(),
        root_id
    );

    Some(RiskOrigin {
        key,
        kind: RiskKind::ReachableRoundingMismatch,
        loc: sink_loc,
        source_param_index: single_param_index(value),
        width: value.width(),
        shift_amount: None,
        threshold: None,
        title: "Semantically related value reaches sink with incompatible rounding modes"
            .to_string(),
        expr_text: expr_text.clone(),
        failed_condition:
            "consistent rounding mode across all reachable paths for this quantity".to_string(),
        path_facts: ctx.path_facts.clone(),
        source_interval: value.interval.describe(),
        source_name: facts
            .root_expr
            .as_ref()
            .map(|r| r.debug.clone())
            .unwrap_or_else(|| "value".to_string()),
        helper_name: Some(ctx.fn_name.to_string()),
        helper_like: false,
        guard_mismatch: false,
        obligation_kind: ObligationKind::RoundingConsistency,
        proof_mode: ProofMode::Abstract,
        rounding_mode: Some(facts.rounding_mode),
    })
}
