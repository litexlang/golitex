# Builtin inference (atomic facts)

When the runtime stores or learns an **atomic** fact, `Runtime::infer_atomic_fact` may derive further facts. This matches the `match` in `src/infer/infer_atomic_fact.rs`. (Composite facts like `And` / `Or` use other `infer_*` paths in `src/infer/infer_dispatch.rs`.)

## `EqualFact`

Implemented in `src/infer/infer_equal_and_normal.rs` (`infer_equal_fact`). Steps are merged in order:

1. **Difference zero** — `0 = a - b` (or symmetric) ⇒ store **`a = b`**.
2. **Numeric binding** — If one side evaluates to a concrete number, bind the other side’s name to that normalized value.
3. **Cart / tuple / finite-seq list / matrix list** — Structural equalities: `IsTuple`, `tuple_dim`, cart metadata, list shapes, as in the Rust helpers.

*Example:* `a = 1 + 2` binds `a` to the normalized value of `3`; `0 = x - y` adds the fact `x = y`.

## `InFact` (membership `x $in S`)

Depends on the shape of `S`:

| RHS `S` | What is inferred | Example |
|--------|------------------|---------|
| `FnSet` | If `element` is identifier-like (`Identifier`, `IdentifierWithMod`, `FieldAccess`, `FieldAccessWithMod`), register it in `known_objs_in_fn_sets`; also re-store the `InFact` | — |
| `ListSet` | **Empty list** ⇒ no inference. Otherwise **OR** of equalities: each list member is one disjunct | `a $in {1,2}` ⇒ `(a = 1) or (a = 2)` |
| `SetBuilder` | `element $in` parameter domain **and** each defining fact with the parameter replaced by `element` | `{ t $in T \| P(t) }` |
| `Cart` | **Fewer than two** cart factors ⇒ no inference. If `n ≥ 2`: `IsTuple(element)`, **`tuple_dim(element) = n`**, cart metadata | `p $in cart(A, B)` |
| `range(a,b)` | `element $in Z`, **`a <= element`**, **`element < b`** | integer half-open interval |
| `closed_range(a,b)` | `element $in Z`, **`a <= element`**, **`element <= b`** | integer closed interval |
| `N_pos`, `Q_pos`, `R_pos` | **`0 < element`** | positive ray |
| `Z_neg`, `Q_neg`, `R_neg` | **`element < 0`** | negative ray |
| `Z_nz`, `Q_nz`, `R_nz` | **`element != 0`** | nonzero |
| `N` | **`element >= 0`** (equivalently **`0 <= element`**) | `k $in N` ⇒ `k >= 0` |
| `Z`, `Q`, `R` | (nothing extra here) | — |
| `FamilyObj` (`\name(args)`) | Instantiate family to a concrete **member set**, then infer as that `InFact` | type-level family |
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

Handled by `infer_numeric_order_sign_from_order_atomic` (see `src/infer/infer_numeric_order_sign.rs`):

1. **Literal on one side only:** when exactly one side is a resolved numeric constant, a sign fact for the **other** side may be stored (`0 < x` or `x <= 0`), according to the relation and the sign of the constant.

2. **Opposite sign via `(-1)*x`:** when **`0` is on the right** (`x < 0`, `x <= 0`, `x > 0`, `x >= 0`), may store the flipped comparison for **`(-1)*x`**. **Not** when **`0` is on the left** (e.g. `0 < x` produced from `x > k` with `k > 0`): storing **`(-1)*x < 0`** would require **`x $in R`** for well-definedness, which often fails for parameters (e.g. `forall a {1,2}:`). Skips operands already of the form `(-1)*u`. Proving **`(-1)*x`** order goals from either side is still available in verification (`try_verify_order_opposite_sign_mul_minus_one` in `number_compare.rs`).

*Examples (infer):* `n < 0` or `n <= 0` may infer **`(-1)*n >= 0`**; `n > 0` or `n >= 0` may infer **`(-1)*n < 0`** / **`(-1)*n <= 0`**.

## `RestrictFact` (`$restrict_fn_in`)

Implemented in `src/infer/infer_in_fact.rs` (`infer_restrict_fact`). When the RHS is a concrete **`fn`** value (`Obj::FnSet`), the **`FnSetBody`** is stored on **`known_objs_in_fn_sets`** for the function **`obj`** as **`KnownFnInfo.restrict_to`**, replacing any previous **`restrict_to`** for that key. **`NotRestrictFact`** still does not infer.

## Other atomic kinds

Everything **not** listed above hits the `_` arm of `infer_atomic_fact`: **no facts are inferred** on this path.

Explicit list (all of these return an empty `InferResult` here):

- `IsSetFact`, `IsNonemptySetFact`, `IsFiniteSetFact`, `IsCartFact`, `IsTupleFact`
- `NotRestrictFact`
- `NotNormalAtomicFact`, `NotEqualFact`
- `NotLessFact`, `NotGreaterFact`, `NotLessEqualFact`, `NotGreaterEqualFact`
- `NotIsSetFact`, `NotIsNonemptySetFact`, `NotIsFiniteSetFact`, `NotInFact`, `NotIsCartFact`, `NotIsTupleFact`
- `NotSubsetFact`, `NotSupersetFact`

Non-atomic facts (`And`, `Or`, `forall`, …) are **not** handled here; see `src/infer/infer_dispatch.rs`.
