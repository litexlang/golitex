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
      infer_equal_fact/      # positive-real power and checked transports
      infer_atomic_except_equality/
        expand_definition.rs     # NormalAtomic param types + iff
        membership_*.rs          # InFact by set former / ops
        subset.rs / superset.rs
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

- Cartesian and tuple equalities remain ordinary checked equalities; they do
  not publish shape predicates or construction dimensions.
- Literal `u − v = 0` → `u = v` is **verify-time**
  `EqualFromKnownDifferenceZero` (not infer)
- Positive-real power membership transport  
  (set-builder / closed-numeric indexes and actual membership/equality special-property facts live on **store indexes**)

Positive-real power transport first checks `0 < a^n` using existing builtin
rules, with a child ceiling capped at BuiltinRule and inherited from the caller.
For a real nonzero square this reuses `EvenPowPositiveFromNonzero`; it avoids
searching for the unnecessary stronger premise `0 < a`. If that bounded check
fails, the existing positive-base/real-exponent route retains the original
caller ceiling. The exponent membership and ordinary inferred-store WD remain
checked. No global permission, state, result shape or user-goal search changes.
Tracer: `examples/infer/equal/nonzero_real_square.lit`.

**Other atomics**

- Exact Cartesian membership publishes each ordinary coordinate's factor
  membership, including zero and one factors. It does not publish
  `$is_tuple`, `tuple_dim`, or indexed-object facts. Struct release uses the
  same coordinate builder for field equalities while preserving field laws.
  Tracers: `examples/infer/atomic/cart_exact_function_coordinates.lit` and
  `examples/stmt_nodes/definition/struct_function_coordinate_bridges.lit`.

- NormalAtomic: param-type projection + one-layer def expand
  (Obj domains in the prop signature are instantiated by call-site args;
  binder names need not match — see
  `examples/infer/atomic/normal_atomic_param_types_renamed_carrier.lit`)
- InFact: list/union/intersect/set_minus, cart, ranges/intervals,
  set-builder, power_set, equal-FnSet / fn_range / finite_seq / seq,
  family_union / index_union / index_intersect / **index_cart**,
  signed/nonzero standard-set sign (`N` / `R+` / `R-` / `R*` …);
  strict positive and negative carriers also publish `x != 0` before later
  inferred division/modulo WD consumes the value. `N` alone does not.
- Order bound → sign spelling and mul-by-(−1) flip are **verify-time** only:
  `OrderSignFromPositive/NegativeLiteralBound`, `OrderFlipMulMinusOne`
- A stored weak lower bound `b <= n` or `n >= b`, with available integer `n`
  and nonnegative `b` certificates, publishes `n $in N` in the same scope.
  `InferWeakIntegerLowerBoundInNResult` retains the bound's source FactId,
  the integer and nonnegative-bound proof results, then the ordinary derived
  store/infer result. Each premise check inherits the caller's ceiling and is
  capped at KnownSpecialProperty; no strategy/forall or permission reset is
  used. An exact visible N-membership guard in the existing membership bucket
  stops the N-to-sign projection cycle. Normal output lists the consequence;
  Detailed output retains its FactId through the existing flat infer projection.
  The tracer is `examples/infer/atomic/weak_integer_lower_bound_in_n.lit`.
- `$is_cart` → dim ≥ 2; Subset / Superset → elementwise forall

The FnRange and indexed-family application builders preserve existing callable
FieldAccess heads as well as identifiers, anonymous functions and templates.
Their checked FnSet/domain/source contracts stay the same. An already displayed
field application is recognized as its own preimage; opaque range members still
publish the ordinary existential, and indexed union/intersection members publish
their fiber existential/universal. Canonical receivers are never stripped or
replaced by another same-named field. Tracers: `atomic/field_fn_range.lit` and
`atomic/field_indexed_family.lit` under `examples/infer/`.

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

## Finite lower set from a stored inclusion

Storing `A $subset B` also publishes `$is_finite_set(A)` when the upper
set's finite certificate is available at the caller's existing permissions,
capped at KnownSpecialProperty. The inference keeps the inclusion FactId,
upper finite proof and derived storage result. It does not recurse through
subset strategies or reset search permissions. Proper inclusion benefits from
its existing definition expansion. No available finite upper proof means no
new finite fact; later strategy verification remains available as before.

This forward consequence makes `finite_set_size(A)` well-defined in the same
quantified scope. Verification alone still does not store truth. Tracer:
`examples/infer/atomic/subset_finite_upper_bound.lit`; focused tests:
`tests/unit/execute/finite_set_cardinality_rules/tests.rs`.

## Positive values from strict lower bounds

Storing `b < x` or `x > b` publishes `0 < x` when `0 <= b` is available
under the inherited permissions capped at KnownSpecialProperty. Numeric
closed bounds and previously stored nonnegative bounds use the same rule.
The result retains the strict source FactId, the checked bound proof and the
derived storage result. This does not search arbitrary order chains. A zero
bound is already a positivity seed and is skipped to avoid re-inference.
Negative or unknown bounds and nonstrict zero bounds do not trigger it.

Tracer: `examples/infer/atomic/strict_lower_bound_positive.lit`;
focused tests: `tests/unit/execute/native_scalar_codomain/mod.rs`.
