use crate::security_analysis::report::SinkKind;

const FIELD_KEYWORDS: &[&str] = &[
    "amount",
    "liquidity",
    "reserve",
    "fee",
    "price",
    "sqrt_price",
    "share",
    "mint",
    "burn",
    "debt",
    "collateral",
    "supply",
];

const CALL_KEYWORDS: &[&str] = &[
    "transfer",
    "mint",
    "burn",
    "swap",
    "add_liquidity",
    "remove_liquidity",
    "redeem",
];

pub fn looks_like_helper(name: &str) -> bool {
    let lowered = name.to_ascii_lowercase();
    ["checked_shl", "checked_shlw", "safe_shl", "safe_shlw", "shift", "shl", "scale"]
        .iter()
        .any(|needle| lowered.contains(needle))
}

pub fn looks_like_financial_name(name: &str) -> bool {
    let lowered = name.to_ascii_lowercase();
    FIELD_KEYWORDS
        .iter()
        .any(|needle| lowered.contains(needle))
}

pub fn looks_like_sink_call(name: &str) -> bool {
    let lowered = name.to_ascii_lowercase();
    CALL_KEYWORDS
        .iter()
        .any(|needle| lowered.contains(needle))
}

pub fn sink_priority(kind: &SinkKind, financial_name: bool) -> u8 {
    match (kind, financial_name) {
        (SinkKind::CallArgument, true) => 3,
        (SinkKind::FieldWrite, true) => 3,
        (SinkKind::PublicReturn, true) => 3,
        (SinkKind::CallArgument, false) => 2,
        (SinkKind::FieldWrite, false) => 2,
        (SinkKind::PublicReturn, false) => 1,
        (SinkKind::ArithmeticUse, _) => 1,
    }
}
