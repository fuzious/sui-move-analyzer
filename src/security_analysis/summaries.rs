use crate::security_analysis::domain::RiskOrigin;
use std::collections::BTreeSet;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReturnSummary {
    pub parameter_dependencies: BTreeSet<usize>,
    pub risky_origins: Vec<RiskOrigin>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionSummary {
    pub returns: Vec<ReturnSummary>,
}

impl FunctionSummary {
    pub fn empty() -> Self {
        Self { returns: vec![] }
    }
}
