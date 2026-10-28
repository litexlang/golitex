# Powers and integer congruence

Congruent integers remain congruent after the same natural power; a supplied
modular inverse remains an inverse after raising both integers to that power.
An integer power is also congruent to the same power of its remainder, without
requiring a separately supplied congruence premise.
The positive modulus may be `1`, the exponent may be `0`, and bases may be
negative or zero. In particular, this follows Litex's natural-power convention
`0^0 = 1`. The generic consumer is:

```litex
thm consume_congruence_power:
    ? forall a,b Z,m N+,n N:
        $nt::main::is_congruent_mod(a,b,m)
        =>:
            $nt::main::is_congruent_mod(a^n,b^n,m)
    release thm nt::main::congruence_power(a,b,m,n)
```

[main.lit](main.lit) checks `17^3 ≡ 2^3 (mod 5)`, a negative base, exponent
zero and a squared inverse modulo `12`. It includes modulus `1` with zero
bases and powers of remainders. [contracts](contracts/main.lit) consume all
three theorems generically.
The [negative controls](negative/expected.json) check missing congruence or
inverse premises, nonnatural exponents, nonpositive moduli, a noninteger base
and an incorrect inverse.

Run `python3 examples/number_theory/congruence_powers/check.py --binary
/path/to/litex --output-dir /path/to/results`. No negative-power, primality,
inverse-existence or new selector contract is claimed.
