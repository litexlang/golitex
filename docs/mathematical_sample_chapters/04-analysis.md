# Why a sequence has at most one limit

A sequence is a function whose input is an index. Convergence says that its
values eventually stay within every requested positive error of a number.
The word “eventually” matters: a different error may require a different
starting index, and two proposed limits may give two different starting indices.

We will prove that these choices cannot give a sequence two distinct limits.
The proof will then justify a second step: defining a limit-value function
on the domain of convergent sequences. Existence, uniqueness and selection
play separate roles in that order.

## Reading the quantifiers

Our sequences have domain $\mathbb N^+=\{1,2,\ldots\}$ and real values.
To say $a_n\to L$ means

$$
\forall\varepsilon>0\;\exists N\in\mathbb N^+\;
\forall n\in\mathbb N^+,
\quad n\ge N\Longrightarrow |a_n-L|<\varepsilon.
$$

The index $N$ may depend on $\varepsilon$, but it must work for every later
$n$. Finding a single close term, or letting $N$ depend on the later index,
would give a different and insufficient condition.

The [complete source](../../showcases/math_concepts_in_litex/10_real_analysis_in_nutshell/main.lit)
names the three layers: closeness on a specified tail, existence of such a
tail, and the demand for every positive error. The following standalone
example includes those definitions and the full constant-sequence proof.

```litex
prop is_tail_close_to(a fn(index N+) R, L R, epsilon R+, n0 N+):
    forall n N+:
        n >= n0
        =>:
            |a(n) - L| < epsilon

prop has_eventual_closeness_to(a fn(index N+) R, L R, epsilon R+):
    exist n0 N+ st {$is_tail_close_to(a, L, epsilon, n0)}

prop has_limit(a fn(index N+) R, L R):
    forall epsilon R+:
        $has_eventual_closeness_to(a, L, epsilon)

template<c R>:
    have fn constant_sequence(n N+) R = c

thm constant_sequence_has_limit:
    ? forall c R:
        $has_limit(\constant_sequence<c>, c)
    claim:
        ? forall epsilon R+:
            $has_eventual_closeness_to(\constant_sequence<c>, c, epsilon)
        claim:
            ? forall n N+:
                n >= 1
                =>:
                    |\constant_sequence<c>(n) - c| < epsilon
            \constant_sequence<c>(n) = c
            \constant_sequence<c>(n) - c = 0
            |\constant_sequence<c>(n) - c| = 0
            0 < epsilon
            |\constant_sequence<c>(n) - c| < epsilon
        by def $is_tail_close_to(\constant_sequence<c>, c, epsilon, 1)
        witness $has_eventual_closeness_to(\constant_sequence<c>, c, epsilon) from 1
    by def $has_limit(\constant_sequence<c>, c)
    $has_limit(\constant_sequence<c>, c)
```

The witness is $N=1$ for every positive error. The proof establishes the
tail inequality before supplying that witness. Introducing a name for
convergence alone would not prove any sequence converges.

## Two tails meet

Suppose $a_n\to L_1$ and $a_n\to L_2$. Assume for contradiction that
$L_1\ne L_2$, and set $d=|L_1-L_2|>0$. Apply each limit hypothesis with
$\varepsilon=d/3$. They supply positive integers $N_1$ and $N_2$ such that
the corresponding estimates hold on their respective tails.

Choose $N_0=N_1+N_2$. Since both starting indices are positive,
$N_0\ge N_1$ and $N_0\ge N_2$. At the same term $a_{N_0}$ we therefore have

$$|a_{N_0}-L_1|<d/3,\qquad |a_{N_0}-L_2|<d/3.$$

The triangle inequality now forces

$$
d=|L_1-L_2|
\le |L_1-a_{N_0}|+|a_{N_0}-L_2|
<\frac{2d}{3}<d,
$$

which is impossible. Hence $L_1=L_2$. The proof needs a single index at
which both estimates hold; comparing a term on one tail with a different
term on the other would not give this contradiction.

Here are the central steps from the source theorem, in its local context.
The preceding part of that theorem has established $d>0$ and made the
chosen error a valid positive real argument.

<!-- litex-source: ../../showcases/math_concepts_in_litex/10_real_analysis_in_nutshell/main.lit -->
<!-- litex:skip-test -->
```litex
        obtain n1 from $has_eventual_closeness_to(a, L1, |L1 - L2| / 3)
        obtain n2 from $has_eventual_closeness_to(a, L2, |L1 - L2| / 3)
        have n0 N+ = n1 + n2
        n0 >= n1
        n0 >= n2
        |a(n0) - L1| < |L1 - L2| / 3
        |a(n0) - L2| < |L1 - L2| / 3
        |L1 - a(n0)| = |a(n0) - L1|
        |L1 - L2| <= |L1 - a(n0)| + |a(n0) - L2|
```

The sum is a convenient common index, not a claim that it is the smallest
one. The ordinary proof could use $\max(N_1,N_2)$ instead.

## A value can be selected after it is determined

Define a sequence to be convergent when it has some real limit. This
definition supplies existence, while the theorem just proved supplies
uniqueness. Together they establish that every convergent sequence has
exactly one real limit.

Only after proving that statement does the source introduce its selector:

<!-- litex-source: ../../showcases/math_concepts_in_litex/10_real_analysis_in_nutshell/main.lit -->
<!-- litex:skip-test -->
```litex
have fn sequence_limit_value by exist!:
    ? forall a fn(index N+) R:
        $is_convergent_sequence(a)
        =>:
            exist! L R st {$has_limit(a, L)}
```

The convergence premise is part of the function's domain condition.
There is no selected value here for a divergent sequence. Nor does the
declaration itself establish convergence for an arbitrary sequence. It turns
a previously proved existence-and-uniqueness result into a usable object.

For the constant sequence with value $5$, the constant-sequence theorem
supplies convergence and limit $5$. Uniqueness forces its selected limit
to be $5$. This conclusion uses no completeness theorem: we already know a
candidate and prove that no other candidate can work.

## Exercises

1. In the uniqueness argument, would $N_0=N_1N_2$ also work for positive
   integer starting indices? What changes if the indices may include zero?
2. Why would choosing $\varepsilon=d$ fail to give the same contradiction?
3. Prove that changing finitely many terms does not change a sequence's limit.

## Answers

1. For positive integers, each factor is at least one, so the product is
   at least each factor. With nonnegative indices, one factor may be zero:
   $0\cdot5=0$ is smaller than $5$. Their maximum works in either convention.
2. The triangle inequality would give only $d<2d$, which is compatible
   with $d>0$. Any fixed error $\varepsilon=\theta d$ with
   $0<\theta<1/2$ gives the required contradiction.
3. If the two sequences agree for $n\ge M$, take a tail index $N$ for the
   original sequence at a chosen error. For $n\ge\max(M,N)$ the values
   agree and satisfy the same estimate. This works for every positive error.

## Continue reading

The [source guide](../../showcases/math_concepts_in_litex/10_real_analysis_in_nutshell/README.md)
describes this relational development and its selector. The separate
[native calculus lecture](../../showcases/analysis/calculus/README.md) develops
derivatives and definite integrals through native analysis interfaces.
The present uniqueness proof does not assert that every sequence converges,
or establish real completeness, series theory or integration.

[Previous](03-topology.md) · [Contents](README.md) · [Next: number theory](05-number-theory.md)

