module reduced::helper_math {
    public fun mul_u128(a: u128, b: u128): u256 {
        (a as u256) * (b as u256)
    }

    public fun div_round(n: u256, d: u256, up: bool): u256 {
        let p = n / d;
        if (up && ((p * d) != n)) {
            p + 1
        } else {
            p
        }
    }
}

module reduced::semantic_rename {
    use reduced::helper_math;

    public fun strange_quote(alpha: u128, beta: u128, gamma: u128): u64 {
        let delta = if (alpha > beta) {
            alpha - beta
        } else {
            beta - alpha
        };
        let omega = helper_math::mul_u128(gamma, delta);
        let sigma = helper_math::mul_u128(alpha, beta);
        assert!(sigma > 0, 0);
        let out = helper_math::div_round(omega, sigma, true);
        (out as u64)
    }
}
