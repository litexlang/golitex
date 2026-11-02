# Finite products and finite choice

This module constructs finite Cartesian products of arbitrary indexed sets,
including zero factors, and proves finite choice by induction. It imports
`set_laws` for the general membership-to-nonemptiness theorem. It uses neither
the Axiom of Choice nor Regularity.

```ini
[import std]
Products = finite_products
[alias]
fp = Products::main
[export]
main = "./main.lit"
```

The empty product contains exactly the empty tuple, even when the family carrier
is empty:

```litex
have empty_family fn(k closed_range(1,0)) {} = tuple()
release thm fp::finite_cartesian_product_zero({},empty_family)
\fp::finite_cartesian_product<0,{},empty_family> = {tuple()}
```

## Construction and contracts

`\fp::finite_cartesian_product<n,S,g>` takes a natural length `n`, a set `S`
of possible factor sets and a complete family `g:closed_range(1,n)->S`. Its
members are complete functions on those indices, returning into `family_union(S)`
and satisfying `p(k) in g(k)` at every coordinate. This is an actual bounded
set of functions. The carrier and factors may be empty; nonemptiness is a
theorem with its own hypotheses.

| Theorem after `fp::` | Contract |
| --- | --- |
| `finite_cartesian_product_member(n,S,g,p)` | A complete function with every required factor membership belongs to the product. |
| `finite_cartesian_product_signature(n,S,g,p)` | A product member has the complete finite function signature. |
| `finite_cartesian_product_factor(n,S,g,p,k)` | A member with that signature has its k-th coordinate in the k-th factor. |
| `finite_cartesian_product_empty_member(S,g)` | `tuple()` belongs to the zero-factor product. |
| `finite_cartesian_product_zero(S,g)` | The zero-factor product equals `{tuple()}`. |
| `finite_cartesian_product_choice(n,S,g)` | If every factor is nonempty, supplies an actual complete selection in the product, also for `n=0`. |
| `finite_cartesian_product_nonempty(n,S,g)` | Under the same hypotheses, the product satisfies `$is_nonempty_set`. |
| `finite_cartesian_product_native(n,S,g)` | For `n in N+` and a nonempty `S`, the construction equals native `index_cart(closed_range(1,n),S,g)`. These are the native constructor's legal-domain conditions. |
| `finite_cartesian_product_empty_factor(n,S,g,k)` | If one legal factor is empty, the product is empty. |

The selection supplied by the existence theorem has the exact function carrier
`fn(k closed_range(1,n)) family_union(S)`. A function with another declared
return carrier needs checked interface evidence or an actual function with
that return carrier. Coordinate membership alone is a separate obligation.

These interfaces implement the n-fold products and finite choice of Tao,
*Analysis I*, 3.5.7 and 3.5.12, including the empty-product convention in 3.5.11.
They preserve native tuple/function semantics. An ordered pair, a nested pair
and a triple keep their distinct complete domains; no tuple flattening or
implicit change of function arity is introduced. Arbitrary infinite products
and their Choice-based nonemptiness remain separate.

## Verification

On 2026-10-31 the existing release executable reporting `1.1.10-beta` accepted
all ten source declarations in strict mode. Independent imports exercise all
nine theorem contracts at full domains, zero factors over an empty carrier,
heterogeneous natural/real factors, an extracted selection and an empty factor.
The complete README example also passes a clean strict run. Five final controls
reject an empty-product/empty-set equality, missing nonempty factors, negative
length, an outside coordinate and a purported member of the empty set.

These are focused source and import gates. No kernel change, source trust,
user axiom, executable build or Lean replay is included. Local development
receipts and unfinished textbook work remain under `experiments/`.
