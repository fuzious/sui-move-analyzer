use move_compiler::{
    hlir::ast as H,
    naming::ast::BuiltinTypeName_,
    parser::ast::BinOp_,
};
use move_core_types::u256::U256;
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Interval {
    pub lower: Option<U256>,
    pub upper: Option<U256>,
    pub bottom: bool,
}

impl Interval {
    pub fn top() -> Self {
        Self {
            lower: None,
            upper: None,
            bottom: false,
        }
    }

    pub fn singleton(value: U256) -> Self {
        Self {
            lower: Some(value),
            upper: Some(value),
            bottom: false,
        }
    }

    pub fn bottom() -> Self {
        Self {
            lower: None,
            upper: None,
            bottom: true,
        }
    }

    pub fn join(&self, other: &Self) -> Self {
        if self.bottom {
            return other.clone();
        }
        if other.bottom {
            return self.clone();
        }
        Self {
            lower: match (self.lower, other.lower) {
                (Some(lhs), Some(rhs)) => Some(lhs.min(rhs)),
                _ => None,
            },
            upper: match (self.upper, other.upper) {
                (Some(lhs), Some(rhs)) => Some(lhs.max(rhs)),
                _ => None,
            },
            bottom: false,
        }
    }

    pub fn intersect(&self, lower: Option<U256>, upper: Option<U256>) -> Self {
        if self.bottom {
            return Self::bottom();
        }
        let lower = match (self.lower, lower) {
            (Some(lhs), Some(rhs)) => Some(lhs.max(rhs)),
            (lhs @ Some(_), None) => lhs,
            (None, rhs) => rhs,
        };
        let upper = match (self.upper, upper) {
            (Some(lhs), Some(rhs)) => Some(lhs.min(rhs)),
            (lhs @ Some(_), None) => lhs,
            (None, rhs) => rhs,
        };
        if let (Some(lo), Some(hi)) = (lower, upper)
            && lo > hi
        {
            return Self::bottom();
        }
        Self {
            lower,
            upper,
            bottom: false,
        }
    }

    pub fn is_singleton(&self) -> Option<U256> {
        match (self.lower, self.upper, self.bottom) {
            (Some(lo), Some(hi), false) if lo == hi => Some(lo),
            _ => None,
        }
    }

    pub fn describe(&self) -> String {
        if self.bottom {
            return "unreachable".to_string();
        }
        match (self.lower, self.upper) {
            (Some(lo), Some(hi)) if lo == hi => lo.to_string(),
            (Some(lo), Some(hi)) => format!("[{lo}, {hi}]"),
            (Some(lo), None) => format!(">= {lo}"),
            (None, Some(hi)) => format!("<= {hi}"),
            (None, None) => "unknown".to_string(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ConstraintOp {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

impl fmt::Display for ConstraintOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self {
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Gt => ">",
            Self::Ge => ">=",
            Self::Eq => "==",
            Self::Ne => "!=",
        };
        write!(f, "{text}")
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PathFact {
    pub var: Option<H::Var>,
    pub op: ConstraintOp,
    pub bound: Option<U256>,
    pub text: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BitFacts {
    pub width: u16,
    pub known_zero: U256,
    pub known_one: U256,
}

impl BitFacts {
    pub fn unknown(width: u16) -> Self {
        let mask = width_mask(width);
        Self {
            width,
            known_zero: U256::max_value() ^ mask,
            known_one: U256::zero(),
        }
    }

    pub fn exact(width: u16, value: U256) -> Self {
        let mask = width_mask(width);
        let value = value & mask;
        Self {
            width,
            known_zero: U256::max_value() ^ value,
            known_one: value,
        }
    }

    pub fn mask(&self) -> U256 {
        width_mask(self.width)
    }

    pub fn join(&self, other: &Self) -> Self {
        let width = self.width.max(other.width);
        let mask = width_mask(width);
        Self {
            width,
            known_zero: (self.known_zero & other.known_zero) | (U256::max_value() ^ mask),
            known_one: (self.known_one & other.known_one) & mask,
        }
    }

    pub fn min_value(&self) -> U256 {
        self.known_one & self.mask()
    }

    pub fn max_value(&self) -> U256 {
        self.mask() & (U256::max_value() ^ self.known_zero)
    }

    pub fn exact_value(&self) -> Option<U256> {
        let mask = self.mask();
        if ((self.known_zero | self.known_one) & mask) == mask {
            Some(self.known_one & mask)
        } else {
            None
        }
    }

    pub fn discarded_bits_may_be_non_zero(&self, discarded_mask: U256) -> bool {
        ((U256::max_value() ^ self.known_zero) & discarded_mask) != U256::zero()
    }

    pub fn shift_left(&self, shift: u8, width: u16) -> Self {
        let mask = width_mask(width);
        Self {
            width,
            known_zero: ((self.known_zero << shift) | low_mask(shift) | (U256::max_value() ^ mask))
                & U256::max_value(),
            known_one: (self.known_one << shift) & mask,
        }
    }

    pub fn shift_right(&self, shift: u8, width: u16) -> Self {
        let mask = width_mask(width);
        let shifted_known_zero = (self.known_zero >> shift) | (U256::max_value() ^ mask);
        let shifted_known_one = (self.known_one >> shift) & mask;
        Self {
            width,
            known_zero: shifted_known_zero,
            known_one: shifted_known_one,
        }
    }

    pub fn bitand(&self, other: &Self, width: u16) -> Self {
        let mask = width_mask(width);
        let known_one = (self.known_one & other.known_one) & mask;
        let known_zero = (self.known_zero | other.known_zero) | (U256::max_value() ^ mask);
        Self {
            width,
            known_zero,
            known_one,
        }
    }

    pub fn bitor(&self, other: &Self, width: u16) -> Self {
        let mask = width_mask(width);
        let known_one = (self.known_one | other.known_one) & mask;
        let known_zero = (self.known_zero & other.known_zero) | (U256::max_value() ^ mask);
        Self {
            width,
            known_zero,
            known_one,
        }
    }

    pub fn bitxor(&self, other: &Self, width: u16) -> Self {
        let mask = width_mask(width);
        let known_one = ((self.known_one & other.known_zero)
            | (self.known_zero & other.known_one))
            & mask;
        let known_zero = ((self.known_zero & other.known_zero)
            | (self.known_one & other.known_one))
            | (U256::max_value() ^ mask);
        Self {
            width,
            known_zero,
            known_one,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SymbolicTerm {
    Unknown,
    Const(U256),
    Var(H::Var),
    AddConst(H::Var, i128),
    Opaque(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RiskKind {
    ReachableShiftTruncation,
    FakeCheckedShift,
    ReachableNarrowCast,
    InvalidShiftCount,
    ReachableLossyRightShift,
    DynamicU256Shift,
    SuspiciousBitwiseArithmetic,
    ReachableWeakDenominator,
}

impl RiskKind {
    pub fn rule_id(&self) -> &'static str {
        match self {
            Self::ReachableShiftTruncation => "security/reachable-shift-truncation",
            Self::FakeCheckedShift => "security/fake-checked-shift",
            Self::ReachableNarrowCast => "security/reachable-narrow-cast",
            Self::InvalidShiftCount => "security/invalid-shift-count",
            Self::ReachableLossyRightShift => "security/reachable-lossy-right-shift",
            Self::DynamicU256Shift => "security/dynamic-u256-shift",
            Self::SuspiciousBitwiseArithmetic => "security/suspicious-bitwise-arithmetic",
            Self::ReachableWeakDenominator => "security/reachable-weak-denominator",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum FormulaTag {
    PriceLike,
    PriceDiff,
    LiquidityLike,
    PriceProduct,
    LiquidityScaled,
    ClmmNumerator,
    ClmmDenominator,
    DenominatorLike,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FormulaFactor {
    pub name: String,
    pub tags: BTreeSet<FormulaTag>,
    pub strict_positive: bool,
}

impl FormulaFactor {
    pub fn new(name: String, tags: BTreeSet<FormulaTag>, strict_positive: bool) -> Self {
        Self {
            name,
            tags,
            strict_positive,
        }
    }

    pub fn join(&self, other: &Self) -> Option<Self> {
        if self.name != other.name {
            return None;
        }
        let tags = self
            .tags
            .intersection(&other.tags)
            .cloned()
            .collect::<BTreeSet<_>>();
        Some(Self {
            name: self.name.clone(),
            tags,
            strict_positive: self.strict_positive && other.strict_positive,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FormulaFacts {
    pub tags: BTreeSet<FormulaTag>,
    pub factors: Vec<FormulaFactor>,
}

impl FormulaFacts {
    pub fn from_name(name: &str, strict_positive: bool) -> Option<Self> {
        let tags = formula_tags_from_name(name);
        if tags.is_empty() {
            return None;
        }
        Some(Self {
            tags: tags.clone(),
            factors: vec![FormulaFactor::new(name.to_string(), tags, strict_positive)],
        })
    }

    pub fn join(&self, other: &Self) -> Option<Self> {
        let tags = self
            .tags
            .intersection(&other.tags)
            .cloned()
            .collect::<BTreeSet<_>>();
        let mut factors = vec![];
        for factor in &self.factors {
            if let Some(other_factor) = other
                .factors
                .iter()
                .find(|candidate| candidate.name == factor.name)
                && let Some(joined) = factor.join(other_factor)
            {
                factors.push(joined);
            }
        }
        if tags.is_empty() && factors.is_empty() {
            None
        } else {
            Some(Self { tags, factors })
        }
    }

    pub fn with_tag(mut self, tag: FormulaTag) -> Self {
        self.tags.insert(tag);
        self
    }

    pub fn merge_tags(&mut self, tags: impl IntoIterator<Item = FormulaTag>) {
        for tag in tags {
            self.tags.insert(tag);
        }
    }

    pub fn all_factors_strict_positive(&self) -> bool {
        !self.factors.is_empty() && self.factors.iter().all(|factor| factor.strict_positive)
    }

    pub fn any_price_like_factor(&self) -> bool {
        self.factors
            .iter()
            .any(|factor| factor.tags.contains(&FormulaTag::PriceLike))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RiskOrigin {
    pub key: String,
    pub kind: RiskKind,
    pub loc: move_ir_types::location::Loc,
    pub source_param_index: Option<usize>,
    pub width: Option<u16>,
    pub shift_amount: Option<u8>,
    pub threshold: Option<U256>,
    pub title: String,
    pub expr_text: String,
    pub failed_condition: String,
    pub path_facts: Vec<String>,
    pub source_interval: String,
    pub source_name: String,
    pub helper_name: Option<String>,
    pub helper_like: bool,
    pub guard_mismatch: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValueState {
    pub interval: Interval,
    pub term: SymbolicTerm,
    pub bit_facts: Option<BitFacts>,
    pub formula_facts: Option<FormulaFacts>,
    pub parameter_dependencies: BTreeSet<usize>,
    pub risky_origins: Vec<RiskOrigin>,
}

impl ValueState {
    pub fn top() -> Self {
        Self {
            interval: Interval::top(),
            term: SymbolicTerm::Unknown,
            bit_facts: None,
            formula_facts: None,
            parameter_dependencies: BTreeSet::new(),
            risky_origins: vec![],
        }
    }

    pub fn with_interval(interval: Interval) -> Self {
        Self {
            interval,
            term: SymbolicTerm::Unknown,
            bit_facts: None,
            formula_facts: None,
            parameter_dependencies: BTreeSet::new(),
            risky_origins: vec![],
        }
    }

    pub fn with_width(width: u16) -> Self {
        let mut value = Self {
            interval: Interval {
                lower: Some(U256::zero()),
                upper: Some(uint_max(width)),
                bottom: false,
            },
            term: SymbolicTerm::Unknown,
            bit_facts: Some(BitFacts::unknown(width)),
            formula_facts: None,
            parameter_dependencies: BTreeSet::new(),
            risky_origins: vec![],
        };
        value.refine_with_bit_facts();
        value
    }

    pub fn exact_uint(width: u16, value: U256) -> Self {
        let facts = BitFacts::exact(width, value);
        Self {
            interval: Interval::singleton(value & width_mask(width)),
            term: SymbolicTerm::Const(value & width_mask(width)),
            bit_facts: Some(facts),
            formula_facts: None,
            parameter_dependencies: BTreeSet::new(),
            risky_origins: vec![],
        }
    }

    pub fn join(&self, other: &Self) -> Self {
        let mut dependencies = self.parameter_dependencies.clone();
        dependencies.extend(other.parameter_dependencies.iter().copied());
        let mut risky = self.risky_origins.clone();
        for origin in &other.risky_origins {
            if risky.iter().all(|existing| existing.key != origin.key) {
                risky.push(origin.clone());
            }
        }
        let mut joined = Self {
            interval: self.interval.join(&other.interval),
            term: SymbolicTerm::Unknown,
            bit_facts: match (&self.bit_facts, &other.bit_facts) {
                (Some(lhs), Some(rhs)) => Some(lhs.join(rhs)),
                _ => None,
            },
            formula_facts: match (&self.formula_facts, &other.formula_facts) {
                (Some(lhs), Some(rhs)) => lhs.join(rhs),
                _ => None,
            },
            parameter_dependencies: dependencies,
            risky_origins: risky,
        };
        joined.refine_with_bit_facts();
        joined
    }

    pub fn width(&self) -> Option<u16> {
        self.bit_facts.as_ref().map(|facts| facts.width).or_else(|| {
            self.interval.upper.and_then(|upper| {
                [8u16, 16, 32, 64, 128, 256]
                    .into_iter()
                    .find(|width| upper <= uint_max(*width))
            })
        })
    }

    pub fn exact_value(&self) -> Option<U256> {
        self.interval
            .is_singleton()
            .or_else(|| self.bit_facts.as_ref().and_then(BitFacts::exact_value))
    }

    pub fn refine_with_bit_facts(&mut self) {
        let Some(facts) = &self.bit_facts else {
            return;
        };
        let lower = Some(facts.min_value());
        let upper = Some(facts.max_value());
        self.interval = self.interval.intersect(lower, upper);
    }

    pub fn may_have_non_zero_bits(&self, mask: U256) -> bool {
        self.bit_facts
            .as_ref()
            .is_none_or(|facts| facts.discarded_bits_may_be_non_zero(mask))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AbstractState {
    pub locals: BTreeMap<H::Var, ValueState>,
    pub path_facts: Vec<PathFact>,
    pub unreachable: bool,
}

impl AbstractState {
    pub fn new() -> Self {
        Self {
            locals: BTreeMap::new(),
            path_facts: vec![],
            unreachable: false,
        }
    }

    pub fn bottom() -> Self {
        Self {
            locals: BTreeMap::new(),
            path_facts: vec![],
            unreachable: true,
        }
    }

    pub fn join(&self, other: &Self) -> Self {
        if self.unreachable {
            return other.clone();
        }
        if other.unreachable {
            return self.clone();
        }
        let mut locals = BTreeMap::new();
        let mut keys: BTreeSet<H::Var> = self.locals.keys().copied().collect();
        keys.extend(other.locals.keys().copied());
        for key in keys {
            match (self.locals.get(&key), other.locals.get(&key)) {
                (Some(lhs), Some(rhs)) => {
                    locals.insert(key, lhs.join(rhs));
                }
                (Some(lhs), None) => {
                    locals.insert(key, lhs.clone());
                }
                (None, Some(rhs)) => {
                    locals.insert(key, rhs.clone());
                }
                (None, None) => {}
            }
        }
        let shared_facts = self
            .path_facts
            .iter()
            .filter(|fact| other.path_facts.contains(fact))
            .cloned()
            .collect();
        Self {
            locals,
            path_facts: shared_facts,
            unreachable: false,
        }
    }
}

pub fn builtin_width(builtin: &BuiltinTypeName_) -> Option<u16> {
    match builtin {
        BuiltinTypeName_::U8 => Some(8),
        BuiltinTypeName_::U16 => Some(16),
        BuiltinTypeName_::U32 => Some(32),
        BuiltinTypeName_::U64 => Some(64),
        BuiltinTypeName_::U128 => Some(128),
        BuiltinTypeName_::U256 => Some(256),
        _ => None,
    }
}

pub fn type_builtin(ty: &H::Type) -> Option<BuiltinTypeName_> {
    match &ty.value {
        H::Type_::Single(single) => single_builtin(single),
        _ => None,
    }
}

pub fn single_builtin(single: &H::SingleType) -> Option<BuiltinTypeName_> {
    match &single.value {
        H::SingleType_::Base(base) => base_builtin(base),
        H::SingleType_::Ref(_, base) => base_builtin(base),
    }
}

pub fn base_builtin(base: &H::BaseType) -> Option<BuiltinTypeName_> {
    match &base.value {
        H::BaseType_::Apply(_, type_name, _) => match &type_name.value {
            H::TypeName_::Builtin(sp!(_, builtin)) => Some(*builtin),
            _ => None,
        },
        _ => None,
    }
}

pub fn uint_max(width: u16) -> U256 {
    match width {
        8 => U256::from(u8::MAX),
        16 => U256::from(u16::MAX),
        32 => U256::from(u32::MAX),
        64 => U256::from(u64::MAX),
        128 => U256::from(u128::MAX),
        256 => U256::max_value(),
        _ => U256::max_value(),
    }
}

pub fn type_interval(ty: &H::Type) -> ValueState {
    match type_builtin(ty).and_then(|builtin| builtin_width(&builtin)) {
        Some(width) => ValueState::with_width(width),
        None => ValueState::top(),
    }
}

pub fn integer_value(value: &H::Value) -> Option<U256> {
    match &value.value {
        H::Value_::U8(v) => Some(U256::from(*v)),
        H::Value_::U16(v) => Some(U256::from(*v)),
        H::Value_::U32(v) => Some(U256::from(*v)),
        H::Value_::U64(v) => Some(U256::from(*v)),
        H::Value_::U128(v) => Some(U256::from(*v)),
        H::Value_::U256(v) => Some(*v),
        _ => None,
    }
}

pub fn is_numeric_binop(op: BinOp_) -> bool {
    matches!(
        op,
        BinOp_::Add
            | BinOp_::Sub
            | BinOp_::Mul
            | BinOp_::Div
            | BinOp_::Mod
            | BinOp_::BitOr
            | BinOp_::BitAnd
            | BinOp_::Xor
            | BinOp_::Shl
            | BinOp_::Shr
    )
}

pub fn width_mask(width: u16) -> U256 {
    uint_max(width)
}

pub fn low_mask(shift: u8) -> U256 {
    if shift == 0 {
        U256::zero()
    } else {
        (U256::one() << shift) - U256::one()
    }
}

pub fn formula_tags_from_name(name: &str) -> BTreeSet<FormulaTag> {
    let lowered = name.to_ascii_lowercase();
    let mut tags = BTreeSet::new();
    if lowered.contains("sqrt_price") || lowered == "price" || lowered.contains("_price") {
        tags.insert(FormulaTag::PriceLike);
    }
    if lowered.contains("price_diff") || (lowered.contains("diff") && lowered.contains("price")) {
        tags.insert(FormulaTag::PriceDiff);
    }
    if lowered.contains("liquidity") {
        tags.insert(FormulaTag::LiquidityLike);
    }
    if lowered.contains("denom") || lowered.contains("denominator") {
        tags.insert(FormulaTag::DenominatorLike);
    }
    tags
}
