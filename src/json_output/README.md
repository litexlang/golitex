# `json_output`

Projects `ExecStmtResult` trees into user-facing JSON. Does **not** change the
verify/exec IR (Lean replay and detail still read the full tree).

## Detail levels

```rust
pub enum OutputDetail {
    Compact,   // thin: success + statement (+ fail_reason)
    Normal,    // current default for all emit paths
    Detailed,  // field-isomorphic IR projection (omit local_env)
}
```

Default CLI / test emit uses **Normal**. **Compact** and **Detailed** are
implemented under `project_compact` / `project_detailed`
(`project_stmt_*` / `project_run_*` / `emit_run_*`).

The native scalar result-type leaf is `InFact.NativeScalarCodomain`.
Normal output explains the checked native codomain (for example `Z` for
`sign(a) $in R`); Detailed output records `rule: "NativeScalarCodomain"` and
`codomain: "Z"`. The enclosing atomic result retains the input WD proof.
Closed numeric expressions keep the existing calculation-membership route.

Detailed atomic WD records argument proofs followed by `predicate_signature`:
an intrinsic builtin signature or an owner-qualified `prop` / `abstract_prop`
signature and its arity. An undefined or wrong-arity user predicate fails at
`predicate_signature`, retaining the successful argument proofs. This failure
is distinct from an argument-object WD failure. Equality stays on its separate
WD path; mixed conjunction/chain evidence uses the intrinsic signature case.

Builtin atomic WD then records `predicate_domain`, whose entries contain the
required carrier/signature fact and its verification evidence. A failed
domain entry retains the completed argument, signature and earlier domain
stages. This prevents malformed builtin predicates from becoming assumptions
merely because their conclusions repeat the same fact.

Whole-forall replay has Detailed `searched_proof.type: by_known_forall_fact`,
with a real `cite_fact_id` and `parameter_renamings` (`source` / `target`
IdentifierIds), followed by the goal WD evidence. The local-introduction
route keeps its introduced parameters, assumed domains and proved conclusions.
Successful `have_fn_by_forall_exist_unique` now exposes `source_forall` and
`fn_set_well_defined`; failures identify the source / FnSet / property stage.
See `examples/stmt_nodes/definition/forall_source_replay.lit` for an unused
outer binder and renamed existential witness.

## Template definition facts

Successful templates expose their published universal definition facts in
Normal `stores` / `infers`. Instance membership can report `cite_forall` with
the stored parameterized fact. Detailed template output includes
`definition_facts`, whose entries retain `source_fact_id` and the enclosing
`store_and_infer` evidence. The source fact belongs to the retained Rust local
environment; that environment is omitted from JSON. Chinese output localizes
these keys as `定义事实`, `来源命题编号`, and `存储与推理`.

## Equality provenance

Structural identity is `they_are_the_same` in Normal output. Detailed output
uses `by_they_are_the_same`, `kind: same_ir | same_free_param_shape`, and a
shape name for alpha evidence. A single `by_equivalence_class` route has either
`kind: known_path` with generating-edge citations, or `kind: via_peers` with
`left_path`, `bridge`, and `right_path`. The bridge includes its equality,
well-definedness proof, and restricted searched proof. No class handle replaces
a FactId citation. Known-atomic Detailed output includes
`why_parameters_of_known_fact_are_equal_to_givens`, exposing these equality
subproofs for membership and other parameter transports. See the
[equality result tree](../execute/execute_fact_stmt/verify_atomic_fact/verify_equality/README.md).

## Induction evidence and failures

Normal induction failures keep the statement-level `why_failed.phase` and add
`why_failed.failure` with the exact stage. Detailed output carries the same
value under `failure`. Stages include `from_in_z`, `goal_wd`, `base`, and
`step`; a failed case has a nested `proof_body` or `goal` reason with a
zero-based `step_index` or `goal_index` and the actual failed result.
Recursive-definition failures retain a `nested_case` path, then `coverage`,
`disjoint`, return WD, or return type, instead of collapsing to one shell.

Successful Detailed induction includes the checked integer base, goal-domain
assumption, goal WD, and `body.base` / `body.step` with their stored assumptions,
ordinary statement results, and verified goals. Recursive-definition Detailed
output contains `case_checks` recursively; `algo ... by induc` retains these
checks under its `define_fn` result. Local environments remain in the
Rust evidence for ownership and replay; they are omitted from JSON as before.
The producer/consumer regression is
`tests/unit/execute/induction_repairs/tests.rs`.

## Compact statement shape

Success — only disposition + source text:

```json
{
  "success": true,
  "statement": "1 + 2 = 3"
}
```

Failure — add a thin `fail_reason` (`phase` + optional `goal`):

```json
{
  "success": false,
  "statement": "a > 10",
  "fail_reason": {
    "phase": "search_proof",
    "goal": "a > 10"
  }
}
```

Chinese (`-lang zh`):

```json
{
  "成功": true,
  "语句": "1 + 2 = 3"
}
```

```json
{
  "成功": false,
  "语句": "a > 10",
  "失败原因": {
    "阶段": "搜索证明",
    "目标命题": "a > 10"
  }
}
```

Compact deliberately omits `proof_method`, `stores`, `infers`, and cite details.
Field order: `success` → `statement` → (`fail_reason` when failed).

## Normal statement shape (frozen)

Success:

```json
{
  "success": true,
  "statement": "1 + 2 = 3",
  "proof_method": {
    "type": "builtin_rule",
    "rule_name": "Calculation",
    "message": "Both sides evaluate to the same number"
  },
  "stores": ["1 + 2 = 3"],
  "infers": []
}
```

Chinese session (`-lang zh`): same shape with **localized field names** and
localized `type` / `phase` / `rule_name` / `message` values (no English tokens
under Chinese keys). Example:

```json
{
  "成功": true,
  "语句": "1 + 2 = 3",
  "证明方法": {
    "类型": "内置规则",
    "规则名": "计算",
    "说明": "两边都算出同一个数"
  },
  "存储": ["1 + 2 = 3"],
  "推断": []
}
```

Key remapping lives in `json_keys.rs` (`localize_key`); authors always write
English keys in code and `object(lang, …)` remaps them. Under `-lang zh`,
emitted `类型` / `阶段` *values* are Chinese too (owned by explain/helper
match arms).

Cited-membership example:

```json
{
  "success": true,
  "statement": "k >= 0",
  "proof_method": {
    "type": "builtin_rule",
    "rule_name": "From known in N",
    "message": "The goal follows from a known natural-number membership",
    "line": 1,
    "cite": "k $in N"
  },
  "stores": ["k >= 0"],
  "infers": []
}
```

Failure:

```json
{
  "success": false,
  "statement": "a > 10",
  "why_failed": { "phase": "search_proof", "goal": "a > 10" },
  "stores": [],
  "infers": []
}
```

Rules:

- `success` is a bool (not `outcome` string).
- Builtin why: print `rule_name` + `message` only (no `rule` / `rule_id` /
  `variant` in Normal JSON). Stable ids live inside `explain/` for tests.
- Builtin why path: call `rule.rule_id_and_message(lang)` only.
  - Atomic: `explain/atomic_builtin_rule/` — every family enum and every leaf
    proof has dedicated EN+ZH copy (no family-level stubs).
  - Equality: `explain/equality_builtin_rule/` (top enum dispatches to each
    leaf; every leaf + Calculation has EN+ZH).
  Projection never matches on rule variants for copy text.
- Non-builtin searched-proof routes (`builtin_strategy`, `by_definition`,
  `equivalence_class`, …) use `explain/searched_proof_why.rs` so they also
  emit `rule_name` + `message` (not a bare `type` tag).
- All Chinese/English copy lives under `json_output/explain/` — verify/exec IR
  stays language-free. `OutputLanguage` comes from `LaunchCommand` (`-lang`).
- Priority of explain coverage:
  1. Every Normal surface has English + Chinese `rule_name` / `message`
     (stmt kinds, compound facts, searched-proof routes, equality leaves,
     every atomic builtin leaf, Calculation).
  2. Detailed projects the full result IR tree and omits `local_env`.
- `stores` / `infers` / `cite` / `statement` / `goal` use `readable_string`
  (IR with `#id#` wrappers stripped), not raw IR and not `fact_id`.
- Cite may include `line` when the cited fact has a source line; omit `line` if unknown.
- Normal skips WD subtrees.

## Detailed statement shape (frozen contract)

Same envelope as Normal run JSON, but `"detail": "detailed"`.

Each statement projects the **result IR fields** recursively:

- `success`, `kind`, `statement`
- nested stage fields (`verify`, `store_and_infer`, WD, searched_proof, …)
- `Fact` / `Obj` as `readable_string`; `FactId` with optional readable cite
- **`local_env` is omitted** at every nesting level (no `ExecEnv` dump)

Does **not** invent `search_trace` / failed-search noise.

Fact success sketch:

```json
{
  "success": true,
  "kind": "fact",
  "statement": "0 <= k",
  "verify": {
    "type": "atomic_except_equality",
    "success": true,
    "fact": "0 <= k",
    "well_defined": { "...": "..." },
    "searched_proof": {
      "type": "known_atomic_fact",
      "cite_fact_id": "f1",
      "cite": "0 <= k"
    }
  },
  "store_and_infer": {
    "stores": [{ "fact_id": "f2", "fact": "0 <= k" }],
    "infers": []
  }
}
```

Chinese (`-lang zh`): field keys remapped (`验证` / `存储与推理` / …); IR
variant tags such as `kind` values may stay English.

## Run envelope

```json
{
  "kind": "run",
  "success": true,
  "target": "eval",
  "path": null,
  "detail": "normal",
  "language": "en",
  "statement_results": [ /* Normal or Detailed stmt objects */ ],
  "session_error": null
}
```

`language` is `en` or `zh` from `-lang` (default `en`). Builtin `rule_name` /
`message` follow this language via `json_output/explain/`.

## Acceptance (Normal + Compact + Detailed)

Locked by `cargo test --lib json_output::` (`acceptance_tests` +
`project_normal_tests` + `project_compact_tests` + `project_detailed_tests`):

1. **Normal success shape / field order**: `success` → `statement` →
   `proof_method` → `stores` → `infers`
2. **Normal failure shape**: `success: false` → `statement` → `why_failed` →
   empty `stores`/`infers`
3. **Compact success**: only `success` + `statement` (no proof_method/stores/infers)
4. **Compact failure**: `success` → `statement` → `fail_reason` (`phase` +
   optional `goal`)
5. **Builtin why (Normal)**: `type` + `rule_name` + `message` only (no `rule` /
   `rule_id` / `variant`)
6. **Cite (Normal)**: readable string, no `#id#` wrappers; optional `line`
7. **Chinese (`-lang zh`)**: field keys remapped; type/phase/rule text Chinese
8. **Stmt kinds**: every catalog kind has bilingual `explain_stmt_kind`
9. **Equality builtins**: all variants bilingual via `rule.rule_id_and_message(lang)`
10. **Searched-proof routes / compound facts**: bilingual `rule_name` + `message`
11. **Run envelope**: `kind` / `success` / `detail` (`normal`|`compact`|`detailed`) /
    `language` / `statement_results`
12. **Detailed**: fact success has `verify` + `store_and_infer`; no `local_env`;
    Chinese keys for top-level Detailed fields; run `detail=detailed`

## API

- `project_stmt_compact` / `project_run_compact` / `emit_run_compact`
- `project_stmt_normal` / `project_run_normal` / `emit_run_normal`
- `project_stmt_detailed` / `project_run_detailed` / `emit_run_detailed`

Projection needs a live `Runtime` so cite `FactId`s can resolve to
`readable_string` text.

Detailed by-contra success includes `closing.fact`, `closing.impossible`
and `closing.negated_impossible`. The last two are the actual typed Fact
verification projections retained after the local scope is taken. Closing
failure reports `closing.phase` as `impossible`, `negate_impossible`, or
`negated_impossible`, with the failed verification or unsupported-negation
message. A failed verification never stands for a proof of the opposite.

Function application WD and body unfolding include `function_equal` in their detailed proofs,
containing the stored equality path from the submitted head to the anonymous
function. Known special-property membership proofs use `cite_property_fact_id`
instead of `cite_definition_fact_id`, since their source may be an ordinary
membership or equality fact. The source fact remains resolvable by FactId.

Anonymous-function WD always includes `body_in_ret_set`, the checked return
membership under its parameter and domain assumptions. This proof is required
for parameter projections as well as other bodies. Struct-instance WD retains
the substituted header type proofs in `requirement_fact_verified`; a failed
argument-domain check projects the failed requirement before accepting WD.
Named `have fn` Detailed results expose `anonymous_fn_well_defined` followed
by `fn_set_well_defined` and `store_and_infer`; failures retain the failed WD
stage.

## Native theorem and calculation evidence

Reserved builtin calls project `builtin_theorem` identity, arguments, ordered
requirements and conclusions. Successful releases retain checked type/premise
proofs, conclusion WD and stored citations; choice-backed nonemptiness has
`axiom_of_choice` provenance. Failure projections preserve lookup, arity,
call shape, parameter type, premise, conclusion WD, selected fact and store
stages. Premise failures include the theorem name, exact goal and zero-based
index. Theorem-definition failures preserve nested proof-statement failures.

WD failure projection is recursive over the existing cause enums. Calculation
Detailed evidence distinguishes `closed_decimal`, `rational` and
`complex_imaginary_unit`. Pure binder renaming inside compound objects uses
`same_free_param_shape` / `compound_obj`; reuse of a checked stored equality
can cite `alpha_endpoints`, with its original FactId, orientation and both
endpoint identity proofs. This does not change stored IR keys.


## Statement boundary evidence

Detailed finite enumeration includes `assignments`: parameter WD and binding
assumptions, premise assumptions, and an outcome. `skipped_false_premise`
contains the premise index and its checked negation; `proved` contains ordinary
nested statement `proof_steps` and each conclusion's verification/store results.
Detailed by-method bodies preserve ordinary `ExecStmtResult` branches, including
nested proof methods. The lexical `local_env` remains omitted from JSON.
Detailed eval success includes `source_well_defined` before its rewritten and
evaluated objects. A failed eval WD is also exposed in Normal
`why_failed.failure`, including the offending source expression and failed WD
stage; its command phase remains `eval`.

Normal let and named-function failures expose their existing WD result under
`why_failed.failure`. Concrete `prop` failures retain `parameter_type`,
`auto_open_struct_layer`, or `iff_fact_well_defined` with the existing nested
cause; Normal uses `why_failed.failure`, and Detailed uses `failure`.
A sketch failure adds the zero-based `step_index` and
the nested Normal `result`. Symbolic eval's `UnsupportedExpression` reports
`cause: "unsupported_expression"`. Finite aggregate eval also reports
`aggregate_budget_exceeded` or `aggregate_range_overflow` in Normal and Detailed
output. Successful Normal eval exposes `evaluated_object` and keeps `stores` and
`infers` empty. Detailed output additionally retains range/set enumeration,
function substitution, algorithm equation evidence, each exact term and running
totals. Aggregate equality and symbolic identities project their dedicated proofs.

Detailed failed lets retain `value_well_defined`. Compound fact statement
labels use the same available full goal text as Normal. Successful nonempty
witnesses include object/set WD, `proof_steps`, and `membership_check`;
existential witnesses include ambient WD, witness type checks, proof steps,
body checks, and the optional `uniqueness_check` (`null` for ordinary exist).
These are projections of existing checked evidence, not additional proof rules.

### Local legacy capability evidence

The elementary arithmetic and trig/complex equality families use named rule
variants in Detailed output. A stored-premise consumer carries the complete
`premise` proof and its domain `requirements`; coordinate extensionality carries
both `real` and `imaginary` proofs and checked `domains`. Finite map cardinality
carries its stored map `certificate`. Normal output keeps the existing bilingual
`rule_name` and `message` contract.

Aggregate evidence also includes `reduce` and `finite_set_reduce`. Each records
its `seed`, enumeration, and chronological terms. A term records both the unary
function application and the binary `operation`, with their WD, beta expansion,
source equality paths and resulting `accumulated_value`. An unordered fold must
pass associativity and commutativity in the enclosing object WD before evaluation.
`FunctionRangeOfFiniteDomain` records function membership and domain finiteness.
The runnable collection is
[`legacy_small_capabilities.lit`](../../examples/proof_nodes/equal/by_builtin_rule/legacy_small_capabilities.lit);
paired rejection and Detailed producer/consumer checks are in
`tests/unit/execute/legacy_small_capabilities/tests.rs`.

`AnonymousFnApplicationInCodomain` reads the literal signature only after
application WD, retaining the applied return set and its equality match.
`FoldInCarrier` similarly reads the homogeneous operation signature after fold
WD and retains its literal signature or stored function-membership proof.
Neither route opens builtin, rewrite or forall search. `ReduceLastStep` retains
nonemptiness, the calculated preceding endpoint and the checked final operation.

`BijectivePreimage` is a unique-existence builtin leaf. Detailed output retains
its stored bijection `certificate` and checked `target_membership`. The shape
has one witness, a single equality `f(x)=y` (either orientation), and a map and
target independent of that witness. Choice-function inference reuses the existing
definition-consequence producer and ordinary known-forall consumer.

`CartesianSize` retains a `factor_finiteness` proof for each factor, while
`SinDifference`, `CosDifference` and `ComplexModulusProduct` are structural
identity leaves under the enclosing equality's checked WD. `ReducePartition`
retains two `bounds` proofs (`start <= cut <= end`) and eight `matches` for
the endpoints, adjacency, functions, operations and initial seed. It preserves
left-fold order and permits an empty second segment; it does not require
associativity or commutativity.

`FiniteSetProductFreshInsertion` retains its freshness/set `premises`, scoped
`pointwise` equality between the original and restricted callback, and the
`factor_expansions` and `factor_equal` proof for the inserted value. The scoped
IR keeps its local environment; Detailed follows the existing aggregate
projection convention and omits that environment. All six leaves have English
and Chinese Normal explanations. Producer/consumer and permission checks are
in `tests/unit/execute/legacy_next_capabilities/tests.rs`; the dedicated runnable
tracers are indexed in `examples/proof_nodes/README.md`.
