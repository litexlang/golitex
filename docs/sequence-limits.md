# Real sequence limits (preview)

`$has_seq_limit(a,L)` states that the complete real sequence `a` converges to
the real value `L`. Its public input is `seq(R)`, equivalently
`fn(k N+) R`. Indices start at 1. A finite sequence, a sequence with missing
indices, or a function on a different complete domain needs an explicit
appropriate construction before it can satisfy this interface.

`lim(a)` selects the unique finite real limit only after a candidate or finite
convergence existence has been proved. WD consumes that evidence; it does not
inspect the sequence body to guess a limit. Even a constant sequence requires
a convergence proof before its limit can be used.

```litex
have fn constant(k N+) R = 3
release thm seq_limit_constant(constant,3)
lim(constant) = 3
lim(constant) + 2 = 5
```

The theorem call proves `$has_seq_limit(constant,3)`. The selected-value rule
then derives `lim(constant)=3` by uniqueness. Without that theorem call or
another convergence proof, the selected value is unavailable. The false
equality `lim(constant)=4` remains rejected.

## Epsilon definition and explicit proofs

The candidate relation means that for every positive real epsilon, there is
a positive natural cutoff N such that every k>=N satisfies
`abs(a(k)-L)<epsilon`. Current existential bodies are quantifier-free. The
native definition therefore uses the equivalent tail/preimage inclusion:

```text
forall epsilon R+:
    exist cutoff N+ st {
        {k N+: k >= cutoff} $subset
            preimage_set(a,{v R: abs(v-L) < epsilon})
    }
```

This is mathematical layout notation; the executable syntax keeps the
existential body on one line. Prove that universal statement, then use
`by def $has_seq_limit(a,L)` or explicitly invoke
`seq_limit_from_epsilon(a,L)`. No convergence value or default is introduced
by declaring the sequence. `seq_limit_tail(a,L,epsilon)` projects an
existential cutoff with that same inclusion from a proved candidate.

The reciprocal-sequence acceptance example supplies the actual epsilon-N
proof using `real_archimedean_natural_upper_bound`; no reciprocal-specific
discovery rule is installed in WD.

See the [complete reciprocal proof](../examples/wd/sequence_limit.lit) and
[equivalent sequence interfaces](../examples/wd/sequence_limit_interfaces.lit).
For worked algebra, squeezing, geometric decay and epsilon-tail applications,
see [common sequence-limit proofs](../examples/wd/sequence_limit_common_proofs.lit).

## Explicit builtin theorems

All signatures below list arguments in call order. Each theorem verifies and
retains its premises. These are native mathematical laws, rather than claims
that the runtime synthesizes epsilon proofs for arbitrary functions.

| Call | Required evidence / result |
| --- | --- |
| `seq_limit_from_epsilon(a,L)` | The displayed epsilon-tail condition; produces `$has_seq_limit(a,L)` |
| `seq_limit_tail(a,L,epsilon)` | Candidate and positive epsilon; produces a cutoff and tail inclusion |
| `seq_limit_constant(a,c)` | Every term equals c; produces limit c |
| `seq_limit_neg(a,A)` | Limit A; produces limit -A for the negated sequence |
| `seq_limit_abs(a,A)` | Limit A; produces limit abs(A) |
| `seq_limit_scale(a,A,c)` | Limit A, real c; produces limit c*A |
| `seq_limit_power(a,A,m)` | Limit A, natural m; produces limit A^m |
| `seq_limit_add(a,b,A,B)` | Limits A,B; produces limit A+B for pointwise addition |
| `seq_limit_subtract(a,b,A,B)` | Limits A,B; produces limit A-B |
| `seq_limit_multiply(a,b,A,B)` | Limits A,B; produces limit A*B |
| `seq_limit_divide(a,b,A,B)` | Limits A,B, B!=0, and every b(k)!=0; produces limit A/B |
| `seq_limit_eventually_equal(a,b,L,N)` | Limit L for a; real sequences a,b equal for every k>=N; produces limit L for b |
| `seq_limit_shift(a,L,m)` | Limit L, natural m; produces limit L for a(k+m) |
| `seq_limit_compare(a,b,A,B,N)` | Limits A,B and a(k)<=b(k) for every k>=N; produces A<=B |
| `seq_limit_squeeze(a,b,c,L,N)` | Limits L for a,c and a(k)<=b(k)<=c(k) for every k>=N; produces limit L for b |
| `seq_limit_unique(a,A,B)` | Two candidates for the same sequence; produces A=B |
| `seq_limit_exists(a,L)` | Candidate L; produces existence of a finite real limit |
| `seq_limit_selected(a)` | Finite-limit existence; produces `$has_seq_limit(a,lim(a))` |

Every eventual cutoff N is in `N+`. The result of each operation must itself
be a complete real sequence. In particular a nonzero limiting denominator
does not make a quotient legal at an early zero denominator. The division
theorem retains the all-indices nonzero premise; authors can explicitly
reindex a legal tail when needed. Order limits are non-strict even when a
sequence inequality is strict.

Two already established candidate facts also support a direct uniqueness
equality. General equality congruence substitutes equal sequences. The
negated relation `not $has_seq_limit(a,L)` is logical negation; failure to
prove a candidate or its WD does not prove its negation.

## Scope and compatibility

Only finite limits of real sequences are included. Function-at-point,
one-sided, infinite-input, infinite-output, limsup and liminf interfaces are
separate increments. `lim(a)` is an object constructor, not a higher-order
function value that can be passed without its argument.

`lim` and `has_seq_limit` are reserved in their respective native roles.
The two pre-existing showcase selectors use the local name
`sequence_limit_value` to preserve their original source-owned definitions
and proofs. Local-only `scripts/` projects are not migrated by this feature.

LaTeX renders sequence-limit notation with a fresh index avoiding source
names. As elsewhere, `-latex` only renders parsed source and reports
`verified: false`. Native sequence-limit proof replay into Lean is currently
unsupported and fails explicitly.
