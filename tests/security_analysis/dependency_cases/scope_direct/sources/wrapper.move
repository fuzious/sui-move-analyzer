module scope_direct::wrapper {
    use scope_transitive::transitive_risk;

    public fun through_transitive(seed: u256): u256 {
        transitive_risk::unsafe_deep(seed)
    }
}
