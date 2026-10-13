# Analysis with Litex

The sequence $1,1/2,1/3,\ldots$ approaches zero. What must a proof of this
statement establish? Given any positive error, it must find a place after
which every term lies within that error of zero. This small question leads us
to limits, their uniqueness and arithmetic, and the meaning of an infinite sum.

Read [analysis.lit](analysis.lit) as a short set of lectures. The mathematical
examples come from the companion [Tao Analysis chapter development](../analysis/README.md).
The lectures call its proved results and use its definitions directly. Follow
a citation into the chapter when you want to read the longer argument.

## How small is small enough?

For error $1/10$, the tenth term of $1/n$ is exactly the error. Starting at
11 gives the strict inequality required by the limit definition. In the
lecture's proof, the decisive estimate is:

<!-- litex:skip-test -->
```litex
abs(Tao::chap6::reciprocal_nat_seq(n) - 0) = abs(1 / n) = 1 / n <= 1 / 11 < 1 / 10
```

Here `n N+` and `n >= 11` are the proof's hypotheses. Chapter 6's
`reciprocal_nat_order_reversing` supplies the comparison. Proving this one
error bound prepares us to read the full convergence statement, whose cutoff
depends on an arbitrary positive epsilon.

## Combining things we already know

A constant sequence has its constant value as a limit. The lecture invokes
the chapter theorem for the constant 3:

<!-- litex:skip-test -->
```litex
release thm Tao::chap6::constant_sequence_has_limit(3)
```

Together with the established limit of $1/n$, the addition law gives the
limit of $3+1/n$. These calls make a familiar mathematical practice visible:
once a result is proved, a later argument can use its statement without
repeating its proof. `Tao` is the dependency name in [litex.config](litex.config),
`chap6` is its sequence-limit chapter, and the remaining name is the result.
The cited proofs remain available in the [chapter source](../analysis/chapter06-sequential-limits.lit).

## From terms to partial sums

The terms $1/2,1/4,1/8,\ldots$ tend to zero. Changing their signs alternately
still gives limit zero; replacing the ratio by -1 produces a bounded sequence
that does not converge. These examples show why hypotheses belong in a theorem.

The final example has terms $1,1/2,1/4,\ldots$ and sum 2. A series sum is a
limit of finite partial sums, not the limit of its individual terms. The
[geometric-series proof](../analysis/chapter07-series.lit) connects the finite
sum identity to a remainder tending to zero.

| Lecture | Question | Longer development |
| --- | --- | --- |
| 1 | When are all reciprocal terms smaller than a given error? | Chapter 6: epsilon tails and reciprocal convergence |
| 2 | Can one sequence have two limits? | Chapter 6: uniqueness |
| 3 | What happens when we add a constant? | Chapter 6: constant convergence and the addition law |
| 4 | Which geometric sequences converge? | Chapter 6: geometric limits and the ratio -1 boundary |
| 5 | What does an infinite sum mean? | Chapter 7: geometric-series formula |

[math_collections.md](math_collections.md) maps the definitions and citations.
The companion development contains selected Chapters 1–8 and Appendix A;
it is not a completed formalization of Tao's *Analysis I*. These lectures
introduce no user axioms or direct `trust`, but inherit the companion module's
explicit foundations and Litex's builtin mathematics. See its
[assumptions and omissions](../analysis/STATUS.md) and this lecture's
[verification record](verification.json). No Lean replay is claimed.
For running Litex, see the [CLI documentation](../../docs/cli.md).
