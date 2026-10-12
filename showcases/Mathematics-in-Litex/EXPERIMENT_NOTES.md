# Conclusions from the MIL-to-Litex experiment

Recorded on 2026-10-11. These are observations from an ongoing migration of selected *Mathematics in Lean* material, not a controlled benchmark between the systems.

The experiment demonstrates that Litex's fact-oriented interface can support a substantial mathematical development. It also exposes costs in moving between equivalent representations and reusing facts across files. The [showcase](README.md) makes the positive evidence inspectable through the actual definitions and proofs.

## What the examples establish

In the parity example, `obtain k from $even(n)` exposes the mathematical witness, and `witness $even(m * n) from m * k` constructs the conclusion. In the inverse-image example, membership facts yield two inclusions and set extensionality closes the equality. In the monoid example, operations and laws belong to a supplied record and support an explicit equality chain.

This way of writing follows recognizable mathematical moves. It is a useful design observation, not a measured readability advantage over Lean, which also supports structured proofs.

## Representation and reuse remain engineering work

The migration encountered explicit membership transport after an established equality, sensitivity to named versus anonymous functions, and different behavior for some same-file versus imported definitions. For example, the defining image equation has the following mathematical shape, where `f` maps `S` to `T` and `A` is a subset of `S`:

```text
\chap4::set_image<S, T, f, A> = fn_range(fn(x A) T {f(x)})
```

A reduced same-file control passed strict verification, while the corresponding cross-file control failed. Its cause was not established. The topology migration used the existing image/preimage adjunction interface rather than adding an assumed defining equation.

The earlier literal empty-preimage route also produced an inference stack overflow when using `set_preimage_empty(X, Y, f)`. Its intended mathematical identity is:

```text
{x X: f(x) in {}} = {}
```

Using native `preimage_set` allowed the relevant topology development to proceed, but did not establish that the old route's recursion problem was fixed. These are checking and reuse observations; they do not by themselves show that the mathematical objects are inexpressible. Earlier failures and independent topology checks are outside the exported module's acceptance claim.

## Library support and language design must be separated

The original [MIL project](https://github.com/leanprover-community/mathematics_in_lean) uses Lean 4 and Mathlib. Their [existing mathematical library](https://leanprover-community.github.io/mathlib-overview) supplies interfaces that this Litex work often had to construct or migrate explicitly. Comparing a library call with a fresh construction would mix library availability with proof-interface cost.

There was no matched comparison of completion time, proof size, failure counts or AI success rates. Those questions need fixed versions, the same mathematical statements, stated library conditions, and separate accounting for proof work and verifier repair.

## Source trust and kernel certification are separate

The exported chapters contain no user `trust` or `axiom`. This is a source-level boundary, not a claim about a minimal or independently certified trusted base. Moving a fact into a builtin rule makes the correctness of that rule part of the implementation review.

Lean tactics construct proof terms checked by its kernel; see the [official tactic documentation](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/). This showcase has not completed corresponding Lean compilation and kernel checking. Litex acceptance and Lean certification must be reported separately.

## Scope and next questions

Chapters 1–8 are distributed as the selected executable module. At the preceding migration checkpoint, Chapter 9 had reached 284 of 577 original source slots, and all 329 existing Chapter 11 slots passed an independent scoped file gate. The latter does not establish the complete C1–C10 dependency chain. Chapters 10, 12 and 13 also retain existing proof debt. None of these later chapters is part of the showcased module.

The strongest engineering inference from the experiment is to improve reliable reuse: equality substitution and member transport, consistent function representations, cross-file definition use, inference termination and actionable diagnostics. Whether those improvements lower human or AI cost should then be measured on held-out mathematical tasks. The current experiment supports the direction; it does not quantify the benefit.
