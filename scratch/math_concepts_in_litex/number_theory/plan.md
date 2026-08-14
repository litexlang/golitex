# Plan: Number Theory

## Reader promise

This file shows Litex at its most natural discrete interface: definitions
produce witnesses, proofs obtain and transform them, induction grows facts,
and named theorems connect definitions to computation. It is a coherent first
course spine, not a survey of advanced number theory.

## Mathematical boundary

Included:

- divisibility on integers, with explicit witnesses;
- elementary divisibility algebra and parity;
- quotient/remainder and the Euclidean algorithm;
- gcd and coprimality, using native computation but proving the mathematical
  contract needed downstream;
- Bezout identity;
- congruence modulo a positive natural and its arithmetic laws;
- linear Diophantine equations; and
- induction where it is the mathematical proof, not merely a stress test.

Explicitly excluded:

- rebuilding native integer arithmetic, `gcd`, `prime`, or `coprime` behind
  shadow predicates;
- a complete prime-factorization/UFD development in the first tranche;
- Chinese remainder theorem until congruence and Bezout are stable (it is the
  first extension candidate, not part of the minimum spine);
- quadratic reciprocity, Diophantine approximation, algebraic or analytic
  number theory; and
- collections of isolated olympiad problems that introduce no new interface.

The stop rule is: the first release ends once Bezout has been consumed to
characterize solvability of `a*x + b*y = c`. CRT may be added only as a second
flagship, without pulling in the rest of elementary number theory.

## Internal architecture

1. **Divisibility relation**: a natural `prop` whose evidence is an integer
   multiplier.
2. **Divisibility laws**: reflexivity, transitivity, addition/subtraction, and
   multiplication compatibility.
3. **Euclidean structure**: quotient/remainder specification and decreasing
   gcd computation.
4. **GCD contract**: common-divisor property, greatestness, sign convention,
   and coprime iff gcd one.
5. **Bezout layer**: existence of integer coefficients; keep the coefficients
   as evidence, not merely the gcd equality.
6. **Congruence layer**: equivalence relation and compatibility with addition
   and multiplication.
7. **Flagship application**: characterize and construct solutions of the
   linear Diophantine equation `a*x + b*y = c`.

## Main theorem chain

```text
divisibility witness
  -> divisibility algebra
  -> quotient/remainder
  -> Euclidean algorithm
  -> gcd contract
  -> Bezout coefficients
  -> gcd(a,b) divides c iff a*x + b*y = c is solvable
  -> explicit Diophantine solution construction
```

Congruence is a side chain sharing divisibility:

```text
d divides (a-b)
  -> a congruent b mod d
  -> equivalence laws
  -> addition/multiplication compatibility
  -> optional CRT extension after the main release
```

## Scratch example ladder

1. `3 | 12 | 60 => 3 | 60` -- current tracer; obtains and composes witnesses.
2. Odd plus odd is even -- familiar witness arithmetic.
3. The Euclidean trace `gcd(252, 198) = 18` -- computation linked to the gcd
   contract rather than accepted as a detached calculator result.
4. Back-substitute the same trace to obtain explicit Bezout coefficients.
5. Solve `252*x + 198*y = 18` with the coefficients -- first consumer.
6. General theorem: `a*x + b*y = c` is solvable iff `gcd(a,b)` divides `c` --
   flagship because it consumes divisibility, gcd, existence witnesses, and
   coefficient scaling.

## Modeling decisions

- divisibility is a `prop`: callers assert it and obtain a multiplier witness;
  the multiplier is not canonical.
- gcd remains the native numeric construction. The file proves reusable named
  theorems about its divisibility and greatestness contract rather than
  defining a competing `gcd`.
- Bezout is first a relation/result exposing coefficient witnesses. Introduce
  a selected coefficient pair only if a downstream algorithm genuinely needs
  a canonical choice and uniqueness can be stated honestly (ordinary Bezout
  coefficients are not unique).
- congruence is a `prop`, not an integer-valued function.

## Lean comparison scene

Use the same Bezout-to-Diophantine theorem. Lean should use the relevant
integer gcd/Bezout library interfaces idiomatically; Litex should show
`obtain`, equality chains, and `witness`. The comparison should highlight that
Lean offers a deep mature algebraic hierarchy, while Litex makes witness flow
especially visible. It must not imply that Lean requires manual witness
management in general or that Litex already matches mathlib coverage.

## Acceptance gates

- The project independently passes the release runner.
- The main chain has no direct `trust`.
- The gcd computation is connected to a stated mathematical contract.
- Bezout coefficients are explicit evidence and are consumed downstream.
- The Diophantine theorem proves both necessity and sufficiency.
- Sign and zero cases are stated, tested, and not silently narrowed from `Z`
  to positive naturals.
- No theorem that already verifies directly through stable Builtin behavior is
  duplicated solely to create a citation.

## Expected downstream consumers

The relation/evidence style is a model for later algebra. Congruence can reuse
the relation vocabulary project once stable. The Diophantine flagship is also
a strong public demo for humans and AI agents because every construction has a
locally checkable witness.
