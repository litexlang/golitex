# Mathematical Design: Number Theory

## Implemented first-version slice

`main.lit` now checks divisibility laws, linear-combination closure, a gcd
certificate with Bezout data, both directions of the gcd/Diophantine
criterion, the explicit `84,30,18` example, and an addition law for congruence.
It contains no direct `trust`.

## Core interface cards

### Divisibility

- **Meaning:** `d` divides `n` when `n = d*k` for some integer `k`.
- **Form:** `prop` with an existential witness.
- **Sketch:** `prop divides_by(d,n Z): exist k Z st {n = d*k}`.
- **Rejected form:** a Boolean/numeric function, or a set construction as the
  only interface; proofs need to obtain evidence.
- **Use:** transitivity, gcd, congruence, and Diophantine necessity.

### GCD

- **Meaning:** the normalized greatest common divisor.
- **First-version form:** `is_gcd_certificate(a,b,d)` packages positivity,
  divisibility of both inputs, greatestness among positive common divisors,
  and a Bezout witness for a supplied `d`.
- **Later value form:** reuse a stable native/standard-library gcd value only
  when its named contract theorems are available to this project.
- **Rejected form:** a second unproved local gcd selector or an opaque numeric
  result with no divisor and Bezout interface.
- **Use:** Bezout, coprimality, Diophantine solvability.

### Bezout relation

- **Meaning:** coefficients `x,y` express the gcd as `a*x+b*y`.
- **Form:** theorem exposing `exist x,y Z`; coefficients are nonunique, so no
  unique-selection function is justified.
- **Rejected form:** `have fn bezout_x/bezout_y by exist!` without a canonical
  normalization proving uniqueness.
- **Use:** construct solutions of linear Diophantine equations.

### Congruence

- **Meaning:** `a` and `b` differ by a multiple of positive modulus `m`.
- **Form:** `prop congruent_mod(m,a,b)` defined through divisibility.
- **Rejected form:** remainder equality as the only definition if it obscures
  sign/modulus conventions; it may appear as an equivalent theorem.
- **Use:** equivalence laws and optional CRT.

### Diophantine solvability

- **Meaning:** existence of integer `x,y` satisfying `a*x+b*y=c`.
- **Form:** a `prop` relation plus a named iff theorem with gcd divisibility.
- **Rejected form:** an arbitrary selected solution pair; solutions are not
  unique and the project does not yet specify a normalization.

## Main dependency DAG

```text
integer arithmetic
  -> divides_by                                      [definition]
  -> divisibility laws                               [proof]
  -> quotient/remainder                              [well_definedness]
  -> Euclidean remainder trace                       [implemented example]
  -> gcd certificate and Bezout coefficients         [implemented proof]
  -> Diophantine solvability iff gcd divides target  [implemented proof]
  -> concrete solution construction                  [implemented proof]

divides_by
  -> congruent_mod                                   [definition]
  -> equivalence and arithmetic laws                 [proof]
  -> CRT                                             [future proof]
```

The primary risk is confusing native computation with the whole proof. A
computed gcd is useful evidence, but the reusable chain must still expose why
that value divides both inputs, why every common divisor divides it, and how
the Euclidean trace yields Bezout coefficients.
