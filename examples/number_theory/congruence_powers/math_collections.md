# Integer congruence and powers

The existing congruence multiplication theorem and reflexivity support induction
on a natural exponent. Natural powers preserve integer carriers, including zero
bases and exponent zero. The existing modular-inverse predicate unfolds to
`a*u ≡ 1`; congruence of powers and `(a*u)^n = a^n*u^n` then give the
inverse-power theorem. Both results retain the positive-modulus domain and do
not assert existence of an inverse. The remainder specialization combines the
existing remainder congruence with the power theorem. All 19 focused checks
pass, including 11 final-only refusals and both installed layouts.
