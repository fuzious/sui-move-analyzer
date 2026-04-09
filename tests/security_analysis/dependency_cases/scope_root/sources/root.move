module root::entry {
    use scope_direct::direct_risk;
    use scope_direct::wrapper;

    public fun quote(seed: u256): u256 {
        direct_risk::unsafe_local(seed) + wrapper::through_transitive(seed)
    }
}
