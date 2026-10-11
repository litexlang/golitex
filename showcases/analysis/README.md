# Building Analysis in Litex

A growing mathematical development inspired by Terence Tao’s *Analysis I*.
This showcase follows a path from natural numbers and maps to finite products
and sequence limits. It demonstrates how definitions and checked facts become
context for later constructions. It is a selected public view of a larger
local development, not a completed formalization of the book.

## From natural numbers to reusable facts

Induction makes an infinite family of inequalities checkable by displaying
its base and successor steps. This complete example appears in
[naturals.lit](naturals.lit):

```litex
thm power_two_lower_bound:
    ? forall n N:
        2^n >= n + 1
    by induc n from 0:
        ? 2^n >= n + 1
        ? from n = 0:
            2^0 = 1 = 0 + 1
        ? induc:
            2^(n + 1) = 2^n * 2^1 = 2^n * 2 >= (n + 1) * 2 = (n + 1 + 1) + n >= n + 1 + 1
```

The theorem can subsequently be used with any natural number. The example
uses Litex’s builtin natural numbers and exponentiation; it does not construct
these operations from Peano axioms.

## From maps to cardinality and products

Equal cardinality is defined by the existence of a bijection. The definitions
in [maps.lit](maps.lit) keep the mathematical steps explicit:

```litex
prop is_injective_fn(S, T set, f fn(x S) T):
    forall x1, x2 S:
        f(x1) = f(x2)
        =>:
            x1 = x2

prop is_surjective_fn(S, T set, f fn(x S) T):
    forall y T:
        exist x S st {y = f(x)}

prop is_bijective_fn(S, T set, f fn(x S) T):
    $is_injective_fn(S, T, f)
    $is_surjective_fn(S, T, f)

prop has_equal_cardinality(S, T set):
    exist f fn(x S) T st {$is_bijective_fn(S, T, f)}
```

[finite_products.lit](finite_products.lit) reuses these definitions. For a
positive number of coordinates, it compares finite sequences whose values
belong to prescribed factors with functions satisfying the same coordinate
conditions. The proof establishes equality of the two represented sets, then
constructs their identity bijection. The finite-index formulation also agrees
with the general coordinate-membership predicate.

This demonstrates a representation bridge in current Litex. It is not a
proof of the existence of arbitrary infinite products, a restoration of the
retired product metadata syntax, or a development of cardinal arithmetic.
The represented finite length is positive; length zero is outside these
product theorems.

Finite products organize values over a finite index set. A sequence instead
uses the positive natural numbers as its index set and asks about the behavior
of its tails. This keeps functions as the common language of the next step.

## From epsilon tails to a limit

The [existing public sequence-limit module](../math_concepts_in_litex/10_real_analysis_in_nutshell/main.lit)
is reused directly by this showcase. It expresses the limit definition through
three predicates:

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
```

A constant sequence uses the first tail index, 1, for every positive epsilon.
Limit uniqueness takes a common index from two tails and uses the triangle
inequality to rule out distinct limits. Existence together with uniqueness
then supports the module’s canonical `lim` selector. The reader can follow
this path in the source: definition, witness, uniqueness, then a reusable
object. The selector is available for sequences satisfying the convergence
condition, not for every sequence.

## Reading map

| Read | Mathematical content | What the example makes visible |
|---|---|---|
| [naturals.lit](naturals.lit) | A power-of-two bound | Base and successor obligations; a reusable theorem |
| [maps.lit](maps.lit) | Injections, surjections, bijections, equal cardinality | Defining a mathematical relationship through functions and witnesses |
| [finite_products.lit](finite_products.lit) | Finite sequences and coordinate-constrained function spaces | Set equality and an explicit identity bijection |
| [Sequence limits](../math_concepts_in_litex/10_real_analysis_in_nutshell/main.lit) | Constant convergence, uniqueness and selection | Epsilon witnesses accumulate into a uniquely specified limit object |

[math_collections.md](math_collections.md) describes the callable interfaces and
their domains. [Coverage and assumptions](STATUS.md) distinguishes these
included examples from the broader chapter development.

## What has been checked

The module registered by [litex.config](litex.config), including its reused
public limit source, passes strict verification with Litex 1.0.6-beta.
[verification.json](verification.json) records the checked version, binary and
source hashes, command and result. There are no user `trust`, `axiom`,
`abstract_prop` declarations or named foundation releases in these selected
sources. This remains verification relative to Litex’s builtin mathematics
and verifier, not an independent kernel soundness result or a Lean check.

For command-line usage, see the repository’s [CLI documentation](../../docs/cli.md).
The source book supplies the mathematical direction; this independent
formalization is not an official edition or a substitute for Tao’s text.
