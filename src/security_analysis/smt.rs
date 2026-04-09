use crate::security_analysis::domain::{AbstractState, ConstraintOp, ValueState};
use move_core_types::u256::U256;

pub mod product {
    use super::*;

    pub fn proven_strictly_positive(lhs: &ValueState, rhs: &ValueState) -> bool {
        let lhs_pos = lhs
            .interval
            .lower
            .is_some_and(|lower| lower > U256::zero());
        let rhs_pos = rhs
            .interval
            .lower
            .is_some_and(|lower| lower > U256::zero());
        lhs_pos && rhs_pos
    }

    pub fn proven_lower_bound(lhs: &ValueState, rhs: &ValueState) -> Option<U256> {
        let lhs_lower = lhs.interval.lower.filter(|&l| l > U256::zero())?;
        let rhs_lower = rhs.interval.lower.filter(|&r| r > U256::zero())?;
        lhs_lower.checked_mul(rhs_lower)
    }

    pub fn definitely_zero(lhs: &ValueState, rhs: &ValueState) -> bool {
        lhs.exact_value().is_some_and(|v| v == U256::zero())
            || rhs.exact_value().is_some_and(|v| v == U256::zero())
    }
}

pub mod shift {
    use super::*;
    use crate::security_analysis::domain::PathFact;

    pub fn path_proves_safe(
        threshold: U256,
        var_facts: &[PathFact],
    ) -> bool {
        var_facts.iter().any(|fact| {
            let implied_upper = match fact.op {
                ConstraintOp::Lt => fact.bound.and_then(|b| {
                    if b > U256::zero() {
                        Some(b - U256::one())
                    } else {
                        None
                    }
                }),
                ConstraintOp::Le | ConstraintOp::Eq => fact.bound,
                _ => None,
            };
            implied_upper.is_some_and(|upper| upper <= threshold)
        })
    }

    pub fn proven_safe(
        lhs_upper: Option<U256>,
        threshold: U256,
        var_facts: &[PathFact],
    ) -> bool {
        lhs_upper.is_some_and(|upper| upper <= threshold)
            || path_proves_safe(threshold, var_facts)
    }
}

pub mod bounds {
    use super::*;

    pub fn proven_in_range(value: &ValueState, lo: U256, hi: U256) -> bool {
        let lower_ok = value.interval.lower.is_some_and(|l| l >= lo);
        let upper_ok = value.interval.upper.is_some_and(|u| u <= hi);
        lower_ok && upper_ok
    }

    pub fn proven_non_zero(value: &ValueState) -> bool {
        value
            .interval
            .lower
            .is_some_and(|lower| lower > U256::zero())
            || value
                .formula_facts
                .as_ref()
                .is_some_and(|facts| facts.all_factors_strict_positive())
    }
}

use crate::security_analysis::domain::PathFact;
use move_compiler::hlir::ast as H;

pub fn path_facts_for_var(state: &AbstractState, var: H::Var) -> Vec<PathFact> {
    state
        .path_facts
        .iter()
        .filter(|fact| fact.var == Some(var))
        .cloned()
        .collect()
}
