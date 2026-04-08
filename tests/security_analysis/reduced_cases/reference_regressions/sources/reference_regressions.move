module reduced::reference_regressions {
    fun helper(seed: u256, noise: u256): u256 {
        let coupon = noise << 1;
        let _keep = coupon;
        seed << 64
    }

    public fun mint_amount(seed: u256, amount: u256): u256 {
        helper(seed, amount)
    }
}
