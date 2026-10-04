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
  store_fact.rs              # shape → known-* indexes + object-keyed special-property facts
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
  (set-builder / closed-numeric indexes and actual membership/equality special-property facts live on **store indexes**)

**Other atomics**

- NormalAtomic: param-type projection + one-layer def expand
  (Obj domains in the prop signature are instantiated by call-site args;
  binder names need not match — see
  `examples/infer/atomic/normal_atomic_param_types_renamed_carrier.lit`)
- InFact: list/union/intersect/set_minus, cart, ranges/intervals,
  set-builder, power_set, equal-FnSet / fn_range / finite_seq / seq,
  family_union / index_union / index_intersect / **index_cart**,
  signed/nonzero standard-set sign (`N` / `R+` / `R-` / `R*` …)
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
| MatrixSet membership | No MatrixSet Obj |
| Symbolic-cart / deep equal-set chase / fn-app unfold | Optional polish, not required |

## Tracers

Set-builder membership projection skips an exact visible fact before recursively
storing that consequence. A stored `s = {x s: 0 = 0}` otherwise projects
`element $in s` from that same already-stored membership indefinitely, including
during a freshly parsed builder's WD check. This guard is local to the builder's
carrier/body projections: it does not change truth lookup, global storage,
permission, or result shapes. A per-call visited queue still projects existing
carrier memberships, including positive And/Chain components, because a carrier
equality may arrive after the original membership. It never selects an Or branch.
New consequences follow the ordinary WD → store → infer path. The maintained strict tracer is
`examples/infer/atomic/set_builder_projection_replay.lit`; focused tests also
cover mutual carrier cycles, repeated body membership, false/undefined rejection,
late carrier definitions, exact free owners, no Or selection, WD locality, and
failed-statement rollback.

One rule → one file under `examples/infer/` (see that README).

```bash
target/release/litex -f examples/infer/atomic/in_index_cart.lit
```

## Object capabilities from facts

`ExecEnv.special_properties` indexes actual `InFact` and `EqualFact` sources.
Atomic storage writes it once; definition executors do not separately register
function or sequence shapes. Querying a function signature may use a stored
function membership or an equality to a literal function/signature, and WD may
transport those sources through stored equality paths. Body unfolding retains
its head-to-anonymous-function equality proof. A signature alone never supplies
a concrete body. Default struct field views are separately marked by typed
definition exits; an ordinary struct membership does not select a default view.

## Dedicated builtin definition consequences

Checked positive `prime`, `coprime`, `proper_subset` / `proper_superset`,
`dvd`, and `bijective` facts publish the consequences built by their existing
canonical definition constructors. Each named result retains its source FactId
and WD-checked stored children. The producer preserves definition order:
`coprime` publishes the non-all-zero disjunction before `gcd=1`; gcd WD can
consume that disjunction without selecting an operand. Divisibility retains
`dvd(x,y)` = “y divides x”, with the existing nonzero divisor requirement.
Negative predicates publish no positive consequences. Quantified unique
preimages and choice-function facts are outside this publication slice.

Acceptance: `examples/example_small_repairs.lit` and
`tests/unit/execute/example_small_repairs/tests.rs`.
