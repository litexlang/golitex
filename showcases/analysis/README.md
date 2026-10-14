# Tao's Analysis I in Litex

Analysis gives meaning to infinite processes by asking precise questions about
finite observations. How can a finite index control every later term of a
sequence? When does a sequence of partial sums approach a real value? What
allows us to choose that value uniquely and use it in a later argument?

This non-strict adaptation follows selected developments from Terence Tao's
*Analysis I*. Induction leads to sets and maps; rational Cauchy sequences lead
to real-number interfaces; completeness supports limits, series and
countability. Definitions and proofs remain in chapter order, so a reader can
follow the mathematical dependencies as well as individual results.

The collection contains selected Chapters 2–8 and Appendix A. Familiar number
systems and operations use Litex builtins; construction and completeness
assumptions remain explicit. Four user axioms and one abstract predicate remain,
so this is not a strict proof development, a complete formalization or an
official edition of the book.

## A small fact inside a larger construction

Chapter 5 includes this complete theorem:

```litex
thm zero_positive_fractional_power:
    ? forall n N+:
        1 / n $in R+
        =>:
            0^(1 / n) = 0
```

The exponent must be positive. Litex checks this result using its builtin
zero-to-positive-real-power rule; an empty theorem body does not supply an
extra assumption. The following nonnegative-root theorem uses this zero case
before treating positive bases. [Read the root development](chapter05-real-numbers.lit).
This does not make every power of zero zero: Litex uses `0^0 = 1`, and negative
powers of zero are undefined.

## From epsilon witnesses to reusable limits

Chapter 6 separates three ideas: closeness on a chosen tail, existence of that
tail, and closeness for every positive epsilon. This is an excerpt of the
actual declarations, to be read in the chapter's context:

<!-- litex:skip-test -->
```litex
prop is_tail_close_to(a seq(R), L R, epsilon R+, n0 N+):
    forall n N+:
        n >= n0
        =>:
            abs(a(n) - L) < epsilon

prop has_eventual_closeness_to(a seq(R), L R, epsilon R+):
    exist n0 N+ st {$is_tail_close_to(a, L, epsilon, n0)}

prop has_limit(a seq(R), L R):
    forall epsilon R+:
        $has_eventual_closeness_to(a, L, epsilon)
```

A convergence proof supplies a cutoff for each epsilon. Uniqueness compares
two tails at a common index; limit laws reuse the resulting vocabulary.
[Chapter 6](chapter06-sequential-limits.lit) continues through subsequences,
limsup, liminf and positive-base power continuity. [Chapter 7](chapter07-series.lit)
then treats an infinite series through its sequence of finite partial sums.
The harmonic-series estimates, alternating-series argument and condensation
test show how inequalities and tail bounds become longer proofs.

## From injections to countability

Chapter 8 describes “at most countable” through an injection into the natural
numbers. Here is its definition, with the earlier chapter dependency visible:

<!-- litex:skip-test -->
```litex
prop embeds_into(S, T set):
    exist f fn(x S) T st {$chap3::is_injective_fn(S, T, f)}

prop is_at_most_countable(X set):
    $embeds_into(X, N)
```

This predicate asks for a function and its injectivity proof; it does not
assert that every set has one. The chapter develops countable unions,
Cantor's power-set argument and product representations. Choice remains part
of the mathematical background. [Read Chapter 8](chapter08-infinite-sets.lit)
and the [assumption boundary](STATUS.md).

## Reading map

| Read | Mathematical progression |
| --- | --- |
| [Chapter 2](chapter02-natural-numbers.lit) | Induction, recursion and natural numbers |
| [Chapter 3](chapter03-set-theory.lit) | Sets, maps, finite cardinality and products |
| [Chapter 4](chapter04-integers-and-rationals.lit) | Formal differences, rational arithmetic and distance |
| [Chapter 5](chapter05-real-numbers.lit) | Rational Cauchy representatives, order, completeness, roots and powers |
| [Chapter 6](chapter06-sequential-limits.lit) | Limits, limit laws, subsequences, limsup and liminf |
| [Chapter 7](chapter07-series.lit) | Partial sums, convergence tests and absolute-convergence rearrangements |
| [Appendix A](appendix-a-logic-and-proof-language.lit) | Logic and proof language; an ordered prerequisite of Chapter 8 |
| [Chapter 8](chapter08-infinite-sets.lit) | Countability, Cantor's argument, products and choice |

[Mathematical interfaces](math_collections.md) explains the main dependencies.
The [manifest](litex.config) preserves their verified export order.
This README supplies the reading path; comment-only introduction exports have
been removed from the executable module.

## What the evidence establishes

The original selected Chapter 8 entry and preceding exports passed a full
non-strict Litex run on 2026-10-13. It reported 190 successful main-file
statements. All ten published source files retain the exact executable lines,
indentation and order from those verified inputs; only inactive prose,
comments and blank lines were removed. [verification.json](verification.json)
records the original binary hash, source hashes and publication checks. These
checks do not establish compatibility with every Litex release.

The retained scope has **zero active direct `trust` statements**, while its
original foundation axioms remain. Scope omissions are not proofs. For space, set-indexed sums, the optional
Riemann rearrangement construction, decimal real uncountability and the
advanced order/Zorn branch are omitted. Chapters 9–11 are not included.
[STATUS.md](STATUS.md) lists the precise boundaries. No Lean replay or
independent kernel soundness result is claimed.

The earlier small [induction](naturals.lit), [map](maps.lit) and
[finite-product](finite_products.lit) examples remain available separately.
Their [dated strict receipt](selected-examples-verification.json) covers the
previous small-example selection, not the current chapter manifest.
For Litex usage, see the [CLI documentation](../../docs/cli.md).
