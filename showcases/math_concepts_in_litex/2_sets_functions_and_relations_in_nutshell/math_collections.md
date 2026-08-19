# Mathematical Design: Sets, Functions, and Relations in a Nutshell

## Purpose and scope

This module introduces the shared language of later mathematics without
building a miniature set-theory library. Its tracer is the theorem that the
successor function is injective. That theorem consumes the ordinary function
interface and Litex's builtin `$injective` predicate, so it checks that the
simple examples compose into a real mathematical statement.

## Native interface inventory

| Mathematical role | Litex interface | Reason for using it |
| --- | --- | --- |
| Natural-number carrier | `N` | Builtin carrier; no local number type. |
| Displayed finite sets | `finite_set` | Carries finiteness directly. |
| Set operations | `union`, `intersect`, `set_minus` | Builtin constructors already expose the intended membership rules. |
| Function image | `fn_range` | Records the actual image of a checked function. |
| Binary-relation carrier | `power_set(cart(N, N))` | A relation is represented as a set of ordered pairs. |
| Injectivity | `$injective(N, N, successor)` | Builtin mapping predicate; no duplicate local definition. |

## Source-defined objects

### `first_set` and `second_set`

- **Ordinary meaning:** The overlapping sets `{1, 2, 3}` and `{2, 3, 4}`.
- **Semantic role:** First-class finite-set values.
- **Litex form:** `have ... finite_set = ...`.
- **Use probes:** Membership of `4` in the union, `2` in the intersection, and
  `1` in the relative difference.

### `successor`

- **Ordinary meaning:** The function `n |-> n + 1` on natural numbers.
- **Semantic role:** Callable construction.
- **Litex form:** `have fn successor(n N) N = n + 1`.
- **Use probes:** `successor(4) = 5`, membership in `fn_range(successor)`, and
  the injectivity theorem.
- **Nearest wrong alternative:** A predicate describing input/output pairs
  would lose ordinary function application and the native range interface.

### `next_relation`

- **Ordinary meaning:** The singleton relation containing `(1, 2)`.
- **Semantic role:** Binary relation.
- **Litex form:** A value of `power_set(cart(N, N))`.
- **Use probe:** `(1, 2) $in next_relation`.
- **Nearest wrong alternative:** A custom relation structure would add fields
  without adding any mathematics needed by this example.

## Theorem spine

### `successor_is_injective`

1. Assume `successor(x) = successor(y)`.
2. Rewrite through the function definition to obtain `x + 1 = y + 1`.
3. Subtract one from both sides to obtain `x = y`.
4. Fold the builtin definition of `$injective`.

## Dependency order

```text
first_set, second_set -> union/intersection/difference membership
successor -> evaluation -> fn_range membership -> successor_is_injective
cart(N, N) -> next_relation -> ordered-pair membership
```

The three branches are intentionally independent. The theorem branch is the
tracer because it exercises declaration, application, arithmetic rewriting,
and a reusable builtin property in one short path.

## Boundary

The module does not introduce equivalence relations, quotient sets, inverse
functions, relation composition, cardinal arithmetic, or Cantor--Bernstein.
Those require a longer dependency chain and belong in later showcases. The
public Litex source adds no axiom, `abstract_prop`, or trusted step.
