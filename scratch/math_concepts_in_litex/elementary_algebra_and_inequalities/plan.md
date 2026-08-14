# Plan: Elementary Algebra and Inequalities

## Reader promise

A reader who knows school algebra should be able to read the first screen,
change a number, and understand why the verifier accepts or rejects the next
line. This project is the collection's front door and proof-calculation
vocabulary, not a compressed high-school curriculum.

## Mathematical boundary

Included:

- equality chains and substitution;
- linear equations and small linear systems;
- polynomial identities and factorization;
- zero-product and case arguments;
- absolute value as a definition plus cases;
- linear and quadratic inequalities;
- radicals with explicit domain conditions;
- two-variable AM-GM and a small family of consequences; and
- elementary sequences only when they exercise induction or a reusable
  algebraic pattern.

Explicitly excluded:

- trigonometry, complex-number theory, combinatorics, probability, and
  statistics;
- limits, derivatives, and any disguised calculus argument;
- a general polynomial decision procedure or a catalogue of contest tricks;
- importing hundreds of solved dataset problems; and
- moving school algebra theorems into the kernel merely to shorten proofs.

The stop rule is: a new item enters only if it introduces a reusable concept,
proof move, or downstream interface. Another instance of an already-covered
calculation remains in a dataset, not this core.

## Internal architecture

1. **Arithmetic language**: Builtin `Z`, `Q`, `R`, order, arithmetic, powers,
   `abs`, and `sqrt`.
2. **Reusable constructions**: interval conditions, arithmetic/geometric mean,
   and named polynomial expressions only when later theorems apply them.
3. **Proof patterns**: equality chain, inequality transport, factorization,
   zero product, cases, contradiction, and domain filtering.
4. **Core results**: linear equation uniqueness, a quadratic root/factor
   bridge, absolute-value cases, square nonnegativity, and AM-GM.
5. **Flagship application**: solve a radical equation while proving the domain
   restriction and rejecting the extraneous squared root.

## Main theorem chain

```text
arithmetic identities
  -> equality substitution
  -> factorization and zero product
  -> linear/quadratic equation solving
  -> order transport and nonnegative squares
  -> absolute-value cases
  -> AM-GM
  -> constrained optimization and radical-equation example
```

Implementation order:

1. A transparent linear equation and one two-equation elimination example.
2. Difference of squares and zero-product cancellation with nonzero evidence.
3. `abs` split into nonnegative/negative cases.
4. Square nonnegativity and quadratic inequalities.
5. AM-GM from `(x - y)^2 >= 0`.
6. Radical-equation flagship: derive the domain, square, factor, and eliminate
   the extraneous root by the original condition.

## Scratch example ladder

1. `3 * x + 2 = 11 => x = 3` -- first equality chain.
2. `(x - 1) * (x - 5) = 0` -- case split or explicit nonzero division.
3. `abs(x) <= 2` -- definition and cases.
4. Two-variable AM-GM -- the current tracer and first named theorem.
5. `x = sqrt(11 - 2*x) + 4 => x = 5` -- flagship because it forces domain
   evidence, algebra, and rejection of an extraneous root.

Only examples 4 and 5 should remain prominent in a polished file. Earlier
examples are scaffolding and may become comments or small local claims.

## Lean comparison scene

Use the same AM-GM statement. Show a short idiomatic Lean proof using the
available arithmetic automation beside the Litex equality/inequality chain.
The message is not that one proof is universally shorter: Lean demonstrates a
mature tactic/library layer, while Litex makes the accumulating mathematical
facts the primary interface. Record versions, imports, and exact checked code
before publishing the comparison.

## Acceptance gates

- The file runs independently with the release runner.
- No direct `trust` occurs in the main chain.
- Every side condition of `sqrt`, division, or cancellation is visible.
- At least one example has an invalid candidate that the proof explicitly
  rejects.
- The final application consumes earlier named concepts or theorems rather
  than repeating their bodies.
- The file stays a coherent path rather than a list of unrelated exercises.

## Expected downstream consumers

Number theory reuses factorization and cases; Euclidean geometry reuses
coordinate algebra and nonnegative squares; linear algebra reuses equality
chains and concrete coordinate calculations.
