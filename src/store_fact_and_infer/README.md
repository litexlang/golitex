# `store_fact_and_infer`

After a seed fact is accepted (or trusted), this module **indexes** it into the
env and may **store routine consequences**. It is not open-ended proof search.

## Layering

| Step | Role |
|---|---|
| `store_fact` | Index by shape into known-\* / ExecEnv (no math consequences) |
| `infer_fact` | Generate extra facts only via `store_inferred_*` |
| `store_fact_and_infer` | `{ store, infer }` for a verified seed |
| `store_inferred_fact_and_infer` | WD-check then store+infer (for infer children) |

Callers verify the seed first. Nested WD/proof inside a statement uses
`verify_*` / `store_*` — not a second `exec_stmt`.

## Layout

```text
store_fact_and_infer/
  store_fact.rs              # shape → known-* indexes (+ FnSet shape on store)
  store_fact_and_infer.rs    # glue: store then infer
  helper.rs
  infer_fact/
    infer_fact.rs            # Fact dispatcher
    infer_and_fact.rs
    infer_or_fact.rs         # NoInfer (intentional)
    infer_chain_fact/        # adjacent atomics + transitive closure
    infer_exist_shaped_fact.rs   # exist! / not exist rewrites
    infer_not_forall_fact.rs
    infer_forall_fact*.rs    # NoInfer (intentional)
    infer_atomic_fact/
      infer_equal_fact/      # cart/tuple shape, positive-real power
      infer_atomic_except_equality/
        expand_definition.rs     # NormalAtomic param types + iff
        membership_*.rs          # InFact by set former / ops
        subset.rs / superset.rs / is_cart.rs
  store_fact_and_infer_result/
    # one result type family per dispatcher / rule group
```

## What is inferred (migrated)

**Non-atomic**

- And / Chain adjacent → atomic infer; Chain also closes transitive edges
- `exist!` → uniqueness forall; `not exist` → De Morgan forall
- `not forall` → exist counterexample
- Or / plain Exist / Forall\* → **NoInfer**

**EqualFact**

- Cart/tuple shape (`$is_cart` / dim)
- Literal `u − v = 0` → `u = v` is **verify-time**
  `EqualFromKnownDifferenceZero` (not infer)
- Positive-real power membership transport  
  (set-builder / anon / closed-numeric / FnSet signature live on **store indexes**)

**Other atomics**

- NormalAtomic: param-type projection + one-layer def expand
- InFact: list/union/intersect/set_minus, cart, ranges/intervals,
  set-builder, power_set, equal-FnSet / fn_range / finite_seq / seq,
  family_union / index_union / index_intersect / **index_cart**
- Carrier → sign / nonnegativity / nonzero is **verify-time** only:
  `FromKnownInNatural`, `FromKnownInPositive/Negative/NonzeroStandardSet`
- Order bound → sign spelling and mul-by-(−1) flip are **verify-time** only:
  `OrderSignFromPositive/NegativeLiteralBound`, `OrderFlipMulMinusOne`
- `$is_cart` → dim ≥ 2; Subset / Superset → elementwise forall

## Intentionally not migrated

| Legacy / table item | Why skip |
|---|---|
| `$fn_eq` / `$fn_eq_in` | Props removed; use `f = g` / `by fn_extension` / bare `forall` |
| `y $in replacement(P,A)` | No `Obj::Replacement`; named via `have by replacement_axiom` |
| `x $in &Struct` | Legacy and Manual: no eager public consequences |
| All `Not*`, `$is_set` / finite / tuple / nonempty | Same as legacy: NoInfer |
| MatrixSet membership | No MatrixSet Obj in new_pipeline |
| Symbolic-cart / deep equal-set chase / fn-app unfold | Optional polish, not required |

## Tracers

One rule → one file under `examples/new_pipeline/infer/` (see that README).

```bash
target/release/litex -f examples/new_pipeline/infer/atomic/in_index_cart.lit
```
