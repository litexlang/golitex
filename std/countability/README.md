# Countability

Tao Analysis I8.1.1-8.1.15: distinct countably infinite, at-most-countable and
uncountable predicates; well ordering; the unique increasing enumeration of
every infinite natural subset; subsets, images, unions, integers, triangular
pairs, natural pairs, products and rationals.

Countable means countably infinite in this source. Empty and finite sets are
at most countable. Uncountable means infinite and not countably infinite.
Every enumeration uses native N, including0, as its complete input domain.

The increasing-enumeration proof constructs the initial minimum and recursively
selects the least member above the previous value. It proves strict growth,
injectivity, surjectivity and uniqueness. Existing real_subsequences supplies
the full natural well-ordering theorem and its least-member selector. The
selector's nonempty natural-subset guard is preserved; no new minimum overload
is introduced. The exact enumeration result is exist!, with no new public
function-valued selector.

The sequence-image proof chooses first occurrences and uses an actual
restriction. The original function keeps its full input domain. The union
proof constructs the actual even/odd interleaving using native quot and %.
Integer negation, triangular ranking, product maps and the fraction map are
actual constructions. The triangular-pair set is
`{pair cart(N,N):pair(2)<=pair(1)}`; its rank is the natural triangular number
of the first coordinate plus the second coordinate. Coordinates are1-based. Before using the imported actual triangular functions,
replay `release obj def cnt::natural_triangular_number` and
`release obj def cnt::triangular_natural_pair_rank`. Replay
`release obj def cnt::triangular_natural_pairs` for its set definition, and
publish actual Cartesian membership before coordinate-containing goals.
The rational proof reuses the native reduced-fraction existence theorem.

No new axiom or trust is introduced. Real uncountability and arbitrary
countable unions requiring choice belong to later work. Source-assigned gaps
needed by these named results are proved; this module does not claim to solve
every independent exercise in8.1.

```ini
[import std]
Countability = countability
[alias]
cnt = Countability::main
[export]
main = "./main.lit"
```

```litex
release thm cnt::native_integers_are_countably_infinite

release thm cnt::native_rationals_are_countably_infinite

release thm cnt::product_of_two_countably_infinite_sets_is_countably_infinite(Z,Q)

release thm cnt::natural_subset_is_at_most_countable({})

have fn constant(n N) {42}=42

release thm cnt::natural_sequence_image_is_at_most_countable({42},constant)

release thm cnt::finite_set_is_not_countably_infinite({42})
```
