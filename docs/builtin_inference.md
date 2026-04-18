# Builtin inference (atomic facts)

When the runtime stores or learns an **atomic** fact, `Runtime::infer_atomic_fact` may derive further facts. This matches the `match` in `src/infer/infer_atomic_fact.rs`. (Composite facts like `And` / `Or` use other `infer_*` paths in `src/infer/infer_dispatch.rs`.)

## `EqualFact`

- **Numeric binding**: If one side evaluates to a concrete number, the other side’s symbol is recorded with that normalized value (environment map).
- **Difference zero**: If one side is `0` and the other is `a - b` (or symmetric), emit **`a = b`**.
- **Cartesian / tuple**: The non-literal side gets **`IsCart` / `IsTuple`**, equality of **dimension** to the literal, and stored cart/tuple structure.
- **Finite sequence / matrix list literal**: The other symbol is associated with that **list** representation.

*Example:* `a = 1 + 2` binds `a` to the normalized value of `3`; `0 = x - y` adds the fact `x = y`.

## `InFact` (membership `x $in S`)

Depends on the shape of `S`:

| RHS `S` | What is inferred | Example |
|--------|------------------|---------|
| `FnSet` | Element (identifier-like) registered in `known_objs_in_fn_sets` | — |
| `ListSet` | **OR** of equalities: each list member is one disjunct | `a $in {1,2}` ⇒ `(a = 1) or (a = 2)` |
| `SetBuilder` | `element $in` parameter domain **and** each defining fact with the parameter replaced by `element` | `{ t $in T \| P(t) }` |
| `Cart` | `IsTuple(element)`, **`tuple_dim(element) = n`**, cart metadata for `n ≥ 2` | `p $in A * B` |
| `range(a,b)` | `element $in Z`, **`a <= element`**, **`element < b`** | integer half-open interval |
| `closed_range(a,b)` | `element $in Z`, **`a <= element`**, **`element <= b`** | integer closed interval |
| `N_pos`, `Q_pos`, `R_pos` | **`0 < element`** | positive ray |
| `Z_neg`, `Q_neg`, `R_neg` | **`element < 0`** | negative ray |
| `Z_nz`, `Q_nz`, `R_nz` | **`element != 0`** | nonzero |
| `N`, `Z`, `Q`, `R` | (nothing extra here) | — |
| `FamilyObj` | Instantiate family to a concrete **member set**, then infer as that `InFact` | type-level family |
| `FiniteSeqSet`, `SeqSet`, `MatrixSet` | Desugar to **`FnSet`**, same as function-space membership, plus stored **`InFact`** into that `FnSet` | — |
| (other) | No inference on this path | — |

## `NormalAtomicFact` (predicate instance `P(...)`)

- Check arguments against **`P`’s parameter types**.
- For each **`iff`** clause in **`P`’s definition**, instantiate with the call’s arguments and **store** those facts.

*Example:* If `P` is defined by several `iff` bodies, those bodies become facts with the current arguments substituted.

## `SubsetFact` (`A $subset B`)

Infer **`forall` fresh `x`:** if **`x $in A`** then **`x $in B`**.

*Example:* `S $subset T` ⇒ every member of `S` lies in `T`.

## `SupersetFact` (`A $superset B`)

Infer **`forall` fresh `x`:** if **`x $in B`** then **`x $in A`**.

*Example:* `T $superset S` ⇒ every `x $in S` satisfies `x $in T`.

## Order atoms (`<`, `>`, `<=`, `>=`)

Handled by `infer_numeric_order_sign_from_order_atomic` **only when exactly one side** is a resolved numeric literal. Then a sign fact for the **other** side may be stored (`0 < x` or `x <= 0`), according to the relation and the sign of the constant (see `src/infer/infer_numeric_order_sign.rs`).

*Example:* `2 < a` may yield **`0 < a`** when the corresponding branch applies.

## Other atomic kinds

Negated atoms, `is_set`, restrict, etc.: **`infer_atomic_fact` returns empty** (no automatic inference on this path).
