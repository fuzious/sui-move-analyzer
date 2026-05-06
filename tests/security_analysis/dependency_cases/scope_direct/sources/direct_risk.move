module scope_direct::direct_risk {
    public fun unsafe_local(seed: u256): u256 {
        seed << 64
    }
}
