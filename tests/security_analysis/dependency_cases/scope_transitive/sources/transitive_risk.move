module scope_transitive::transitive_risk {
    public fun unsafe_deep(seed: u256): u256 {
        seed << 64
    }
}
