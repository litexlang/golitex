# Equinumerosity and finite cardinality

This module defines equal cardinality for arbitrary sets by existence of a
bijection. It proves the equivalence laws and connects the source definition
of finite cardinality with native finite sets and `finite_set_size`. The
connection includes zero cardinality and makes no finite-set assumption in
the general equinumerosity definition.

```ini
[import std]
Cardinality = cardinality
[alias]
card = Cardinality::main
[export]
main = "./main.lit"
```

## Definitions

| Predicate | Meaning |
| --- | --- |
| `has_equal_cardinality(X,Y)` | There is a complete bijection `X -> Y`. Both sets may be infinite or empty. |
| `has_n_elements(X,n)` | `X` has equal cardinality with `closed_range(1,n)`, for `n in N`. The initial segment is empty when `n=0`. |
| `has_finite_cardinality(X)` | Some natural `n` satisfies `has_n_elements(X,n)`. |

No second cardinality selector is introduced. On native finite sets the unique
natural cardinal is the existing `finite_set_size(X)`. To compute with a set
known finite only through the source predicate, first publish its native finite
certificate, then call the size theorem.

## Theorems

All names below follow `card::`.

| Theorem | Contract |
| --- | --- |
| `equal_cardinality_reflexive(X)` | Every set has equal cardinality with itself. |
| `equal_cardinality_symmetric(X,Y)` | Equal cardinality can be reversed. |
| `equal_cardinality_transitive(X,Y,D)` | Compose two supplied equinumerosities. |
| `equal_cardinality_finite_transfer(X,Y)` | Native finite `X` and equal cardinality imply native finite `Y`. |
| `has_n_elements_is_finite(X,n)` | A source natural cardinal implies native finiteness of `X`, without that as an extra premise. |
| `finite_set_has_n_elements(X)` | Native finite `X` has source cardinal `finite_set_size(X)`. |
| `initial_segment_size(n)` | `finite_set_size(closed_range(1,n))=n`, including zero. |
| `equal_cardinality_native_size(X,Y)` | Native finite equinumerous sets have equal native sizes. |
| `has_n_elements_native_size(X,n)` | For native finite `X`, its source cardinal equals its native size. |
| `native_size_has_n_elements(X,n)` | A native finite size equality gives the source cardinal. |
| `finite_cardinality_unique(X,n,m)` | Two natural cardinals of an arbitrary set are equal. |
| `positive_cardinality_nonempty(X,n)` | Positive source cardinality implies native nonemptiness. |
| `remove_member_cardinality(X,n,point)` | Removing a member from a set of positive source cardinal `n` gives cardinal `n-1`. |
| `finite_cardinality_is_native_finite(X)` | The source existential finiteness property implies native finiteness. |
| `native_finite_has_cardinality(X)` | Native finiteness implies the source existential property. |
| `naturals_have_no_finite_cardinality` | The natural numbers have no finite cardinal. |
| `finite_image_size_bound(X,Y,f)` | A map from finite `X` into arbitrary `Y` has finite image of size at most `size(X)`. |
| `finite_sequence_init_coordinate(Y,n,v,k)` | The actual prefix restriction preserves coordinate `k`, for `k` in `1..n`. |
| `finite_sequence_successor_equal_cardinality(Y,n)` | Length `n+1` value tables are equinumerous with a length `n` table paired with one value. Works for every set `Y`. |
| `finite_sequence_size(Y,n)` | For finite `Y`, length `n` tables have size `size(Y)^n`, including zero length and empty `Y`. |
| `finite_function_space_equal_cardinality(X,Y)` | For finite `X` and arbitrary `Y`, complete functions `X -> Y` are equinumerous with length `size(X)` value tables. |
| `finite_function_space_is_finite(X,Y)` | The complete function space between two finite sets is finite. |
| `finite_function_space_cardinality(X,Y)` | That space has source cardinal `size(Y)^size(X)`, without a nonemptiness premise. |

The last theorem reuses the existing native infinity of `N` and the proved
source/native connection. The native finite enumeration and finite-bijection
size laws are also reused foundations, not newly introduced axioms or new
implementations of natural numbers.

The prefix construction is `\finite_sequence_init<Y,n>(v)`, with input
`v in finite_seq(Y,n+1)` and result in `finite_seq(Y,n)`. It is an actual
restriction, including the unique empty restriction at `n=0`. Before evaluating
`v(k)` in a caller, publish `k in closed_range(1,n+1)` when only the shorter
index bound is present; `1 <= k <= n < n+1` proves this directly.

For a theorem without universal parameters, omit argument parentheses:
`release thm card::naturals_have_no_finite_cardinality`.

## Example

With the configuration above, this complete caller counts the nine maps from
a two-element set to a three-element set:

```litex
release thm card::finite_function_space_cardinality({0,1},{10,20,30})
finite_set_size({0,1}) = 2
finite_set_size({10,20,30}) = 3
finite_set_size({10,20,30})^finite_set_size({0,1}) = 3^2 = 9
$card::has_n_elements(fn(x {0,1}) {10,20,30},9)
release thm card::finite_function_space_is_finite({0,1},{10,20,30})
release thm card::has_n_elements_native_size(fn(x {0,1}) {10,20,30},9)
finite_set_size(fn(x {0,1}) {10,20,30}) = 9
```

The same general theorem covers an empty domain (one empty function), a
nonempty domain with empty codomain (no functions), and two empty sets
(`0^0=1`). Concrete size and power equalities should be stated explicitly
before using a numerically simplified cardinality predicate.

These results and the existing native finite union, subset, injective-image
and Cartesian-product laws cover Tao, *Analysis I*, section 3.6, including all
six clauses of 3.6.14. Countability and infinite-cardinal arithmetic belong to
later sections and are not claimed here. Drafts and acceptance records remain
under `experiments/`.
