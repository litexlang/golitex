# Modeling And Naming Examples

Read the relevant section when a textbook concept's carrier/form choice or
public-interface name is non-obvious.

## Positive-integer set carrier

Source: “Every nonempty set of positive integers has a least element.”

Do not place the set in `Z` and rebuild “positive integer” as a predicate:

```litex
# Bad: the type is too broad and the first predicate repeats type facts.
prop is_positive_integer_set(S power_set(Z)):
    S $subset Z
    forall x S:
        x $in Z
        x > 0

prop is_least_element_of_integer_set(S power_set(Z), m Z):
    S $subset Z
    m $in S
    forall x S:
        x $in Z
        m <= x
```

Model the domain before the relation. `N_pos` carries “positive integer,” and
`power_set(N_pos)` carries “set of positive integers”:

```litex
prop is_least_element_of_positive_integer_set(S power_set(N_pos), m N_pos):
    m $in S
    forall x S:
        m <= x
```

Put `$is_nonempty_set(S)` on the subsequent well-ordering theorem. The
least-element relation is correctly a `prop`; the discarded carrier predicate
is wrong because it adds no interface beyond existing types. If later code
must apply a selected value such as `min(S)`, expose it as
`have fn ... by exist!` after existence and uniqueness are available.

## Topology interface naming

Use `has_xxx` for witness/value relations and `is_xxx` for judgments or
properties:

```litex
prop has_point_in_epsilon_neighborhood(X set, x R, epsilon R_pos):
    X $subset R
    exist y X st {y $in R, abs(x - y) < epsilon}

prop is_adherent_point(X set, x R):
    X $subset R
    forall epsilon R_pos:
        $has_point_in_epsilon_neighborhood(X, x, epsilon)

prop is_closure_of(C, X set):
    C $subset R
    X $subset R
    forall x C:
        $is_adherent_point(X, x)
    forall x R:
        $is_adherent_point(X, x)
        =>:
            x $in C

prop is_closed_subset(X set):
    $is_closure_of(X, X)

prop is_epsilon_neighborhood_inside(X set, x R, epsilon R_pos):
    forall y R:
        abs(x - y) < epsilon
        =>:
            y $in X

prop is_open_subset(X set):
    X $subset R
    forall x X:
        exist epsilon R_pos st {$is_epsilon_neighborhood_inside(X, x, epsilon)}

prop is_sequence_in_subset(a seq(R), X set):
    X $subset R
    forall n N_pos:
        a(n) $in X
```
