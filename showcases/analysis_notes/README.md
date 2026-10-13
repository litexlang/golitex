# Analysis with Litex

The sequence $1,1/2,1/3,\ldots$ approaches zero. What must a proof establish?
Given any positive error, it must find a place after which every term lies
within that error of zero. This small question leads us to limits, their
uniqueness and arithmetic, and the meaning of an infinite sum.

[analysis.lit](analysis.lit) is a self-contained set of short lectures. It
introduces its definitions and proves its results in one file, using Litex's
builtin real numbers, natural numbers and arithmetic. No textbook module or
external mathematical library is imported. The mathematical direction is
inspired by Terence Tao's *Analysis I*; these are selected lectures rather than
a translation of the book.

## How small is small enough?

We begin with the reciprocal sequence:

```litex
have fn reciprocal(n N+) R = 1 / n

reciprocal(1) = 1
reciprocal(2) = 1 / 2
reciprocal(10) = 1 / 10
```

For error $1/10$, the tenth term is exactly the error. Starting at 11 gives
the strict inequality required by the definition. The first proof establishes
this concrete tail estimate; the next lets the error be arbitrary and uses
the Archimedean property to choose a finite cutoff.

The definition separates a chosen tail, the existence of a suitable tail,
and the requirement that every positive error have such a tail:

```litex
prop is_tail_close_to(a seq(R), L R, epsilon R+, start N+):
    forall n N+:
        n >= start
        =>:
            abs(a(n) - L) < epsilon

prop has_eventual_closeness_to(a seq(R), L R, epsilon R+):
    exist start N+ st {$is_tail_close_to(a, L, epsilon, start)}

prop has_limit(a seq(R), L R):
    forall epsilon R+:
        $has_eventual_closeness_to(a, L, epsilon)
```

The proof supplies the existential witness with `witness`, checks every term
on the tail, then establishes the defined limit property with `by def`.
The source contains this whole argument, not just the convergence assertion.

## Comparing and combining limits

Two proposed limits can be compared on a common tail. If their distance were
positive, errors smaller than a third of that distance would contradict the
triangle inequality. This proves uniqueness while leaving the choice of
cutoff free.

A constant sequence is already at its limit. For a sum of two convergent
sequences, give each input half the allowed error and choose a tail that works
for both. The lectures prove this addition law before applying it to $3+1/n$.
The definitions, general proofs and concrete applications all remain in the
same file.

## From terms to partial sums

Induction gives $2^n\ge n+1$. Taking reciprocals compares the geometric sequence
$(1/2)^n$ with $1/n$ and proves convergence to zero. Alternating the signs
preserves the decaying absolute values. The sequence $(-1)^n$ provides a
contrast: it remains bounded but cannot approach one limiting value.

Finally, define each partial sum of $1+1/2+1/4+\cdots$ by adding one more term.
Induction gives

$$
S_n=2-2(1/2)^n.
$$

The remaining error is $2(1/2)^n$, which tends to zero. Thus the partial sums
have limit 2, even though the individual terms have limit zero. The file
contains the recursive definition, the finite-sum identity and the epsilon
proof of this final limit. It treats this particular series directly; it does
not introduce a general infinite-summation operator.

| Section | Mathematical question |
| --- | --- |
| 1 | What does it mean for every term on a tail to be close? Why does $1/n$ tend to zero? |
| 2 | Why is a limiting value unique? |
| 3 | How do constants and addition interact with limits? |
| 4 | Why do geometric sequences decay? Why is boundedness insufficient? |
| 5 | How can an infinite sum be defined through finite partial sums? |

[math_collections.md](math_collections.md) explains the local interfaces.
[verification.json](verification.json) records strict verification of both
the registered file and a config-free copy. The lecture contains no user
`trust`, `axiom` or `abstract_prop`; it still relies on Litex's builtin
mathematics and verifier. No Lean replay or independent kernel soundness
result is claimed. For running Litex, see the [CLI documentation](../../docs/cli.md).
