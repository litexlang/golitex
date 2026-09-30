# Mathematical Design: A Small Set-Theoretic Chapter

## Purpose and tracer

This showcase is a compact first chapter about sets and functions, not a list
of isolated membership checks. Its concrete tracer is
`successor_moves_first_set_to_second_set`: Litex enumerates the finite domain
`{1, 2, 3}` and verifies that the rule `x |-> x + 1` lands in `{2, 3, 4}`.
That fact then supports three presentations of the same function.

The chapter follows one mathematical line:

```text
membership and extensionality
    -> a finite mapping theorem
    -> a checked function
    -> its graph as a set of ordered pairs
    -> unique output
    -> function selected by `have fn ... by exist!`
```

## Native interface inventory

| Mathematical role | Native Litex interface | Use in this chapter |
| --- | --- | --- |
| Natural numbers | `N` | Ambient carrier for the successor graph. |
| Displayed finite sets | `finite_set` | Concrete domains that `by enumerate finite_set` can exhaust. |
| Set union | `union` | A nontrivial equality proved by extensionality. |
| Set equality | `by extension` | Reduces equality to the two membership directions. |
| Restricted function | `have fn f(x A) B = ...` | Checks that the formula maps `A` into `B`. |
| First-class function value | `fn(x A) B {...}` | Packages the same mapping as an object. |
| Binary relation | `power_set(cart(A, B))` | Represents a graph as a set of ordered pairs. |
| Unique selection | `have fn ... by exist!` | Turns a proved unique-output relation into a callable function. |

No local replacement is introduced for a builtin set, Cartesian product,
function carrier, or unique-existence form.

Current migration boundary: `by enumerate finite_set` requires a displayed
finite domain; it does not resolve a named set before enumerating it. The
ambient natural-number membership is proved directly from `first_set $subset N`.
The successor mapping theorem and its downstream function definitions remain
blocked; the dependency diagram below describes the intended mathematical chain.

## Interface cards

### `first_set` and `second_set`

- **Meaning:** The overlapping finite sets `{1, 2, 3}` and `{2, 3, 4}`.
- **Form:** First-class values of builtin `finite_set`.
- **Use probes:** Their union is computed extensionally; enumeration proves
  that adding one sends every member of the first set to the second.

### `successor_on_first`

- **Meaning:** The restricted map `x |-> x + 1` from `first_set` to
  `second_set`.
- **Form:** Formula-defined `have fn`.
- **Dependency:** Its codomain check consumes the earlier enumeration theorem.

### `successor_as_value`

- **Meaning:** The same restricted map, now stored as a first-class value.
- **Form:** An anonymous `fn(input first_set) second_set {...}` expression.
- **Reason to include:** It distinguishes defining a named callable function
  from constructing a function object that can be stored or passed around.

### `successor_graph`

- **Meaning:** The relation `{(x, y) in N x N : y = x + 1}`.
- **Form:** A set builder inhabiting `power_set(cart(N, N))`.
- **Use probe:** The value selected by unique existence lies on this graph.

### `successor_from_unique_output`

- **Meaning:** The function selected from the relation `y = x + 1`, after
  proving that every input has exactly one output.
- **Form:** `have fn ... by exist!`.
- **Verifier boundary:** Eliminating named graph membership inside the nested
  uniqueness proof currently adds administrative proof steps. The public
  proof uses the equivalent equation `y = x + 1` for selection, then proves
  graph membership as a separate specification theorem. No trust is added.

## Dependency order

```text
first_set, second_set
    |-> first_union_second
    |-> successor_moves_first_set_to_second_set
            |-> successor_on_first
            |-> successor_as_value

N x N |-> successor_graph
unique output |-> successor_from_unique_output
successor_graph + selected output |-> selected_successor_lies_on_graph

first_set subset N + the three definitions
    |-> three_successor_presentations_agree
```

## Boundary

This is deliberately smaller than a full set-theory or analysis chapter. It
does not develop axiomatic set theory, inverse images, equivalence relations,
quotients, cardinal arithmetic, or Cantor--Bernstein. Those require their own
dependency chains. The public Litex source adds no axiom, `abstract_prop`, or
trusted step.
