use crate::security_analysis::report::SinkKind;
use move_compiler::{hlir::ast as H, sui_mode::SUI_ADDR_VALUE};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SemanticCallSink {
    /// Known transfer/movement APIs in the Sui framework.
    KnownAssetMovementApi,
    /// Call escapes the currently analyzed graph (out-of-scope or unresolved callee).
    ExternalBoundary,
}

impl SemanticCallSink {
    pub fn is_critical(self) -> bool {
        matches!(self, Self::KnownAssetMovementApi)
    }

    pub fn label(self) -> &'static str {
        match self {
            Self::KnownAssetMovementApi => "known-asset-movement-api",
            Self::ExternalBoundary => "external-boundary-call",
        }
    }
}

pub fn classify_call_sink(call: &H::ModuleCall, callee_known: bool) -> Option<SemanticCallSink> {
    if is_known_asset_movement_api(call) {
        return Some(SemanticCallSink::KnownAssetMovementApi);
    }
    if !callee_known {
        return Some(SemanticCallSink::ExternalBoundary);
    }
    None
}

fn is_known_asset_movement_api(call: &H::ModuleCall) -> bool {
    // These are framework-level movement/ownership APIs where passing a risky value is meaningful.
    const TRANSFER_FUNS: &[&str] = &[
        "transfer",
        "public_transfer",
        "share_object",
        "public_share_object",
        "freeze_object",
        "public_freeze_object",
        "receive",
        "public_receive",
    ];
    if TRANSFER_FUNS
        .iter()
        .any(|fun| call.is(&SUI_ADDR_VALUE, "transfer", *fun))
    {
        return true;
    }

    // Coin operations that consume/produce value and frequently use amount-bearing inputs.
    const COIN_FUNS: &[&str] = &[
        "transfer",
        "split",
        "split_and_transfer",
        "take",
        "put",
        "join",
    ];
    COIN_FUNS
        .iter()
        .any(|fun| call.is(&SUI_ADDR_VALUE, "coin", *fun))
}

pub fn sink_priority(kind: &SinkKind, critical_surface: bool) -> u8 {
    match kind {
        SinkKind::CallArgument => {
            if critical_surface {
                3
            } else {
                2
            }
        }
        SinkKind::FieldWrite => 3,
        SinkKind::PublicReturn => {
            if critical_surface {
                3
            } else {
                1
            }
        }
        SinkKind::ArithmeticUse => 1,
    }
}
