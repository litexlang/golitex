# `store_fact_and_infer`

After a seed fact is accepted (or trusted), this module **indexes** it into the
env and may **store routine consequences**. It is not open-ended proof search.

## Layering

| Step | Role |
|---|---|
| `store_fact` | Index by shape into known-\* / ExecEnv (no math consequences) |
| `infer_fact` | Generate direct facts only via `store_inferred_fact` |
| `store_fact_and_infer` | `{ store, infer }` for a verified seed |
| `store_inferred_fact` | Direct store only; no WD-cache write (`remember_formed` stays on the user `store_fact_and_infer` path). Correctness belongs to the named infer rule. |

Forward inference runs once per seed. Each named rule guarantees formation and
truth of its direct conclusions from the checked source and its own applicable
conditions. Conclusions store without another WD or inference pass. A later
explicit statement can verify a stored conclusion and use it as a new seed.
`StoreInferredFactResult { store }` records the actual storage stage. The owning
infer enum retains the rule identity, source IDs and genuine condition proofs.
Lean uses this instance data with a proved rule and certified constructors from
`Litex.lean`; it does not need a fabricated conclusion-WD result.
Inference permissions remain disabled in temporary scopes used for checking
rule premises, so those checks cannot open another inference chain.

The strict acceptance file is
[`one_step_store_only.lit`](../../examples/infer/atomic/one_step_store_only.lit).
It covers exact and mutual FnRange cycles, growing builder elements and the
explicit next-seed boundary.

The [acceptance checkpoint](one_step_acceptance.md) records the passing gates
and any remaining verification work. The former derived-WD failure-policy
question is superseded by named-rule direct storage.
The [post-migration loop recheck](loop_recheck.md) records the current call-path
audit, additional cycle/growth controls and the remaining finite chain cost.

[`infer_result/`](infer_result/README.md) owns the typed result tree:
`InferResult` mirrors `Fact`, `InferAtomicFactResult` mirrors every atomic
constructor, and each atomic family contains all matching named rules in
execution order. Fixed conclusions have named fields; Cartesian factors and
builder conditions retain their original indices.

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
    infer_plain_exist_fact.rs    # no inference
    infer_exist_unique_fact.rs   # uniqueness forall
    infer_not_exist_fact.rs      # De Morgan forall
    infer_not_forall_fact.rs
    infer_forall_fact*.rs    # NoInfer (intentional)
    infer_atomic_fact/
      infer_equal_fact/      # scalar cancellation and positive-real power transport
      infer_atomic_except_equality/
        infer_normal_atomic_fact.rs # param types + iff
        infer_in_fact.rs          # membership rule dispatcher
        infer_*_fact.rs           # builtin definition families
        membership_*.rs          # InFact by set former / ops
        subset.rs / superset.rs
  store_fact_and_infer_result/
    # seed {store, infer}, stores and direct inferred stores
  infer_result/
    infer_result.rs              # exhaustive Fact result
    infer_atomic_fact_result.rs  # exhaustive AtomicFact result
    infer_*_fact_result.rs       # per-family named rule enums
    # dedicated rule results and captured child stages
```

## What is inferred (migrated)

**Non-atomic**

- And / Chain adjacent → atomic infer; Chain also closes transitive edges
- `exist!` → uniqueness forall; `not exist` → De Morgan forall
- `not forall` → exist counterexample
- Or / plain Exist / Forall\* → **NoInfer**

**EqualFact**

- Scalar sums with a directly identical common addend publish equality of the
  remaining operands. Scalar products do the same when the common factor has
  an available nonzero certificate. Addition/multiplication match all four
  binary positions; subtraction/division match same positions only. Differences
  cancel a common minuend or subtrahend without nonzero conditions. Quotients
  cancel a nonzero common denominator, or a nonzero common numerator with both
  remaining denominators nonzero. Matching uses exact ObjIR; no alias traversal,
  expansion or reassociation is performed. Three C-membership proofs and all
  required nonzero proofs
  inherit the caller's permissions capped at KnownSpecialProperty. Missing
  premises skip the rule without rejecting the accepted source equality.
  Each result retains the source FactId, common operand, premise proofs and
  direct rule-certified store. The equality graph skips
  already-known endpoints. Each cancellation removes one outer
  arithmetic constructor; a derived equality does not cancel again automatically. Later nonzero facts do not retrigger older seeds.
  Tracers: `examples/infer/equal/{additive,subtractive,nonzero_factor,common_denominator,nonzero_numerator}_cancellation.lit`; focused tests:
  `equality_cancellation`. The five named cancellation families have reviewed
  Lean adapters; other consumed inference families still require their own
  adapter and visible original producer.
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
fails, the positive-base fallback and real-exponent membership use the same
inherited BuiltinRule ceiling. Missing optional evidence skips this inference;
rule premise checking retains the original caller ceiling. No global
permission, state or user-goal search changes. The result retains the selected
positivity proof and real-exponent proof for each successful transport. Tracers:
`examples/infer/equal/nonzero_real_square.lit` and
`examples/infer/equal/positive_real_power_bounded_premises.lit`.

### Optional premise search boundary

| Inference | Ceiling for optional truth premises |
|---|---|
| Positive-real power transport | BuiltinRule |
| Scalar addition/subtraction/product/quotient cancellation | KnownSpecialProperty |
| Strict lower bound to positivity | KnownSpecialProperty |
| Weak integer lower bound to natural membership | KnownSpecialProperty |
| Subset of a known finite upper set | KnownSpecialProperty |

These ceilings are inherited restrictions, never fresh root permissions.
An unavailable optional premise leaves the accepted seed intact. Explicit
proofs can establish and store the missing certificate for a later seed.

Template builder projection expands a checked source instance. Preimage
projection retains its complete-domain certificate and directly constructs its
builder; the inferred builder and projected conclusions do not repeat WD. Both
retain the caller's permissions and required evidence. Every inferred store
still passes through ordinary fact WD. Capping or omitting those checks merely
because they occur during inference would change the formation contract.

Focused release coverage for this boundary and its recursive consumers:

```bash
cargo test --release --lib -- store_fact_and_infer:: function_preimages native_scalar_codomain finite_set_cardinality_rule chain_fact mixed_equality_order_chain
```

The [2026-10-11 call audit](optional_premise_audit.md) records the complete
optional/construction classification and the executed positive/negative gates.

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
  Optional iff children use the existing soft inferred-store path: unavailable
  WD at the inherited caller ceiling skips that child instead of aborting the
  checked seed. No child is stored without its WD evidence and no search ceiling
  is raised. Explicit definition proofs retain their normal obligations.
  Tracer: `examples/infer/atomic/normal_atomic_expand_bounded_wd.lit`.
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
  store result. Each premise check inherits the caller's ceiling and is
  capped at KnownSpecialProperty; no strategy/forall or permission reset is
  used. An exact visible N-membership guard in the existing membership bucket
  stops the N-to-sign projection cycle. Normal output lists the consequence;
  Detailed output retains its FactId through the existing flat infer projection.
  The tracer is `examples/infer/atomic/weak_integer_lower_bound_in_n.lit`.
- Subset / Superset → elementwise forall. Removed Cartesian shape predicates
  produce no dimension facts.

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

Set-builder membership projection stores only the seed's immediate carrier and
body clauses. It skips exact visible consequences, visits no descendant
memberships and never selects an Or branch. A carrier equality arriving later
can be consumed by an explicit new membership statement. Cartesian membership
stored by that projection does not automatically publish coordinates; an
explicit Cartesian seed can do so. The older
`examples/infer/atomic/set_builder_projection_replay.lit` describes the carrier
replay boundary; `one_step_store_only.lit` owns the new termination contract.

One rule → one file under `examples/infer/` (see that README).

```bash
target/release/litex -f examples/infer/atomic/in_index_cart.lit
```

## Object capabilities from facts

`ExecEnv.special_properties` separates actual membership and selected-view rows
from directional equality citations, bucketed by the opposite endpoint's
specific constructor. `SetBuilder`, `ListSet`, `Cart`, range and other readers
have distinct buckets; there is no general `SetStructure` bucket. Source ASTs
and FactIds remain in `facts_by_id`. See the [index contract](../exec_env/README.md).
Structural readers use those exact local sources and declarations;
they do not expand the subject's equality class. A literal anonymous-function
equality supplies a body and its signature directly. Carrier inference reads
only a directly indexed FnSet/seq/finite_seq definition, and stores its checked
consequences through the existing infer interfaces. Chained carrier aliases
need an explicit endpoint before the membership is introduced. Set-builder,
power-set and subset projection use the same exact-property boundary.
A signature alone never supplies a numeric body. Ordinary fact/equality
proving can establish and publish the required membership or equality first.

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
