# `json_output`

Projects `ExecStmtResult` trees into user-facing JSON. Does **not** change the
verify/exec IR (Lean replay and detail still read the full tree).

Normal, Compact and Detailed run projections preserve the complete parsed statement
text retained by the runner. Names, arguments and selected theorem conclusions
stay in `statement`; published facts remain in `stores`. A failed expression
such as `1 / 0 = 0` keeps that source text, with `why_failed.phase: well_defined`
and an explicit localized message that well-definedness could not be proved.
Standalone statement projections without source context use
`<well_defined_not_proven>` when the result tree lacks the original goal.
Session errors use readable Runtime diagnostics rather than Rust Debug wrappers.
Extraction artifacts use the same command metadata on success and failure:
`format`, `target`, `path`, `output_path`, and `language`. `content` is null on
failure; `error` is null on success. Artifact field names follow `-lang` just
like run envelopes; the English schema applies with `-lang en`.

## Detail levels

```rust
pub enum OutputDetail {
    Compact,   // thin: success + statement (+ fail_reason)
    Normal,    // current default for all emit paths
    Detailed,  // field-isomorphic IR projection (omit local_env)
}
```

A successful `eval` publishes the checked `source = result` equality through
`store_fact_and_infer`. Normal output includes `evaluated_object`, `stores`
and `infers`; Detailed output retains the original/re-written source, rewrite
citations, checked algorithm equations, result-equality WD, real `fact_id`
and `store_and_infer`. The calculation trace is its proof certificate. A failed
computation or result check publishes no equality.

Default CLI / test emit uses **Normal**. **Compact** and **Detailed** are
implemented under `project_compact` / `project_detailed`
(`project_stmt_*` / `project_run_*` / `emit_run_*`).

Detailed atomic builtin rewrites retain their variant and checked payload:
closed-numeric and known-equality substitution include `rewritten_fact`,
`cited_equal_fact_ids`, and `proof_of_rewritten_fact`; function unfolding
includes `unfold_equal_proofs`; order duality includes `alternate_fact` and
`proof_of_alternate_fact`. For `n=16 => $prime(n+1)`, this exposes the actual
equality citation and residual `$prime(16+1)` calculation. This is a projection
of existing evidence; see `atomic/by_builtin_rewrite/closed_numeric_prime.lit`.

Detailed predicate registrations identify `property` (`reflexive`, `symmetric`,
or `transitive`) and retain the existing `prop` and checked `forall_proof`.
Rejected registrations expose the actual shape, missing-definition, arity,
or forall-proof stage under `failure`, including its existing child result.
The retained local environment is omitted as elsewhere in Detailed output.
See `examples/stmt_nodes/register/registered_property_evidence.lit`.

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

Atomic WD then records `predicate_domain`. Fresh checks use an array whose
entries contain the required carrier/signature fact and its verification
evidence. Reusing an already checked atomic fact instead produces
`{type: "by_known_fact_domain", cite: ...}`; the citation includes its FactId
and identity/stored-path argument matches. Arguments and the visible signature
are still checked before this reuse, and a new assumption is not stored until
its WD has succeeded. A failed
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

Failed templates retain the outer Normal `why_failed.phase: def_template`
and expose the existing typed child reason under `why_failed.failure`.
Detailed output exposes the same reason under `failure`. The projection
distinguishes parameter WD, automatic struct opening, domain WD, every
supported definition-body family, and unsupported-body messages. It does
not rerun verification or publish a failed template.

For example, `template<a R>: have selected Z = a` retains the path
`body_have_equal -> membership -> search_proof` and the actual failed goal
`a $in Z`. An undefined reciprocal function body retains its selected
anonymous-function WD failure and `x != 0`. Existential body WD failures
also retain their inner reason instead of stopping at a `well_defined`
shell. A successful template's output remains unchanged. See
`examples/test_function_sets/diagnostics/p09.lit`, its paired N26/N27
fixtures, and `json_output::template_failure_tests` for execution gates.

Template-alias application WD adds `function_equal` to the
`template_definition` signature evidence. Tuple result/projection Detailed
output keeps `subject_equal`, `function_equal`, and the template instance with
its signature matches. `FnTupleValue` additionally records `expanded_body` and
`value_equal`; `FnTupleProjection` records `index` and `component_equal`.
Normal output continues to use the existing known-property or enclosing
class-path explanation.

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
  `variant` in Normal JSON). The owning proof type or enum identifies the rule.
- Builtin why path: call `rule.rule_name_and_message(lang)` only.
  - Atomic: `explain/atomic_builtin_rule/` — every family enum and every leaf
    proof has dedicated copy in all ten languages (no family-level stubs).
  - Equality: `explain/equality_builtin_rule/` (top enum dispatches to each
    leaf; every leaf + Calculation covers all ten languages).
  Projection never matches on rule variants for copy text.
- Non-builtin searched-proof routes (`builtin_strategy`, `by_definition`,
  `equivalence_class`, …) use `explain/searched_proof_why.rs` so they also
  emit `rule_name` + `message` (not a bare `type` tag).
- All localized copy lives under `json_output/explain/` — verify/exec IR
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

For a hard internal conflict, `session_error` contains
`internal_bug: Litex internal bug: <specific reason>` and the run has
`success: false`. Normal, Compact and Detailed retain the same reason. Other
session-error strings keep their existing representation; ordinary proof
failure remains a statement result rather than an internal-bug session error.

`language` is the canonical locale from `-lang`: `en`, `zh`, `zh-hant`, `fr`, `ru`, `es`, `ar`, `ja`, `ko`, or `vi` (default `en`). Builtin `rule_name` /
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
8. **Stmt kinds**: every catalog kind has localized `explain_stmt_kind`
9. **Equality builtins**: all variants localized via `rule.rule_name_and_message(lang)`
10. **Searched-proof routes / compound facts**: localized `rule_name` + `message`
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

Detailed equality `fn_application_parent_checked_beta` references the enclosing
equality WD using `parent_well_defined_side` (`left`, `right` or `both`). A named
body retains its checked input signature and equality path. The route retains
`expanded_body`, `residual_equal` and the success-only `residual_proof`. It does
not fabricate a second WD certificate at the residual's restricted permission.
Residual stored-equality paths preserve `cite_fact_id` and endpoints; readable
`cite` text remains conditional on the source fact being visible in the live
runtime when projected.

`fn_application_both_function_bodies` retains separate checked bounded
normalizations for the left and right applications, followed by the residual
equality proof. Curried application layers remain separate in each expansion.

Native `fn_set_member` and default function-space membership retain a
`function_domain` stage before pointwise return proofs. It records function and
target WD, the checked complete-domain source, equality transport paths and
either domain alpha equality or both inclusion proofs. Failures identify the
missing source, arity or failed inclusion stage. `by fn_extension` retains both
complete-domain sources before its pointwise proof and reports the actual
failed stage. Return upper bounds are not domain identity.

Native tuple coordinate equality projects `function_domain` as
`tuple_exact_domains`, retaining separate `left` and `right` complete-domain
proofs before coordinate premises. Both `release thm` and selected `by thm`
use this evidence; a domain mismatch fails before publishing equality.
The Cartesian definition route projects `by_object_definition` with kind
`cart_function_set_definition`, the full expanded set and its actual alpha
match. It does not project the retired CartReconstruction leaf. Normal output
uses the existing localized object-definition explanation.

The whole-forall `empty_parameter_domain` route retains the checked empty
carrier equality, scoped store and full goal WD. Its conclusions are not
projected as independently published facts. New evidence keys are localized
in all supported output languages; source expressions and citation IDs remain
unchanged.

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

Failed claim, sketch, cases, extension and contradiction blocks also retain
their existing typed failure stage. Normal uses `why_failed.failure`; Detailed
uses `failure`. A nested proof-body failure includes its zero-based
`step_index` and failed child result; cases preserve the branch index and
extension preserves `left_to_right` or `right_to_left`. Existing contradiction
`closing` output remains available. Projection neither re-executes proof steps
nor publishes their local facts.

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

`FiniteSetProductFreshInsertion` retains its freshness/set `premises`, actual
callback agreement under `pointwise`, and the
`factor_expansions` and `factor_equal` proof for the inserted value. The scoped
agreement distinguishes same-function, literal-restriction, checked function
equality and scoped pointwise proof. The enclosing equality WD owns the actual
callback domains; a literal restriction never narrows the source function's
membership. Scoped IR keeps its local environment; Detailed follows the existing
aggregate projection convention and omits it. All six leaves have English
and Chinese Normal explanations. Producer/consumer and permission checks are
in `tests/unit/execute/legacy_next_capabilities/tests.rs`; the dedicated runnable
tracers are indexed in `examples/proof_nodes/README.md`.

`SinHalfPiShift` and `CosHalfPiShift` are real-domain identity leaves.
`CosDoubleAngle`, `SinPiReflection`, `CosPiReflection`,
`SinHalfPiReflection` and `CosHalfPiReflection` are further fixed real-domain
leaves under the enclosing equality's complete WD certificate. Detailed
projects the matched `angle` for each. `CosDoubleAngle` additionally projects
`form`: `cosine_square_minus_sine_square`, `one_minus_twice_sine_square`, or
`twice_cosine_square_minus_one`. These identify the checked RHS form rather
than a recursive expansion trace. Each rule has a distinct Normal explanation
in all ten output languages. Search order, ceiling and state remain unchanged.
`ReduceFirstStep` records `nonempty` and five structural `matches`, keeping
the seed as the first operation argument. `ReduceTranslation` records the
integer `shift`, endpoint/operation/seed matches, the fresh `parameter`, two
interval `assumptions`, checked `function_expansions`, and `pointwise` evidence.
Its proof IR retains the binder local environment; the projection follows the
existing aggregate convention and omits it.

`ReducePointwise` records four interval/operation/seed matches and a
`certificate` of type `by_known_forall_fact`: the complete matched `fact`,
real stored `cite_fact_id`, and `parameter_renamings`. It consumes an exact
already checked whole proposition, including optional interval domain facts;
it neither opens general forall search nor publishes global function equality.
`FiniteSetProductMemberRemoval` records membership/set `premises`, the same
callback agreement under `pointwise` and `factor_expansions` / `factor_equal` for the
removed value. Zero factors remain valid. All six leaves have English/Chinese
Normal explanations. The consumer regressions are in
`tests/unit/execute/legacy_final_capabilities/tests.rs`.

## Direct closed calculation

Both equality and non-equality searched-proof enums have `ByClosedCalculation`.
Normal output explains exact closed evaluation in English/Chinese. Detailed
output uses `type: "by_closed_calculation"`, with `kind` identifying equality,
order polarity, membership or non-membership. Equality/disequality retain a
`values` object (decimal/rational normal forms, exact complex coordinates, or
canonical radical objects). Radical equality/disequality uses
`representation: "radical"` and `left_normal`/`right_normal`, for example
`sqrt(12)+sqrt(27)=5*sqrt(3)` retains `5 * sqrt (3)` on both sides;
order retains `left_normal`, `right_normal`, and the actual `comparison`;
membership retains `value` and `set`. Calculation carries no fabricated FactId.
Existing stored citations and identity/alpha paths keep their existing labels.
The Direct entry result also distinguishes `NotFound`, which is not a proof.


## Direct structural membership

`DirectAtomicFactSearchResult::ByStructuralMembership` becomes the corresponding
non-equality searched-proof variant. It has a separate tree from closed values.
Normal output uses `by_structural_membership` / `结构归属`; Detailed retains
`element`, `set`, and `kind`. Arithmetic nodes retain their child proofs; a
`known` leaf retains its original citation, `closed` retains exact calculation,
and `standard_superset` retains the source membership. Intrinsic codomain,
division and power nodes identify `enclosing_object_wd` as their domain evidence:
the sibling fact WD certifies that expression and its subobjects. Search alone
does not establish WD. No synthetic FactId replaces a derived constructor proof.
The regression test inspects nested power/subtraction/known certificates and
both Normal output languages.

## Output languages

`-lang` supports English (`en`), simplified Chinese (`zh`), traditional Chinese
(`zh-hant`), French (`fr`), Russian (`ru`), Spanish (`es`), Arabic (`ar`),
Japanese (`ja`), Korean (`ko`), and Vietnamese (`vi`). Existing `english` and
`chinese` aliases are retained; `zh-hans` also selects simplified Chinese.
The other language names (`french`, `russian`, `spanish`, `arabic`, `japanese`,
`korean`, `vietnamese`) are accepted. Tokens are case-insensitive.

Non-English locales translate known JSON field names, Normal proof types,
Normal/Compact failure phases, rule names, and explanation messages. Unknown
field names keep their English spelling, as before. Detailed IR variant/stage
tags retain their existing machine-oriented spelling. Source statements,
formulas, names, paths, citations, numeric values, booleans and Detailed machine
rule tags remain independent of locale. Arabic output does not insert
bidirectional control characters into source or JSON. Human-facing English/Chinese copy may
be corrected alongside the other locales; source text and Detailed machine
tags remain stable.

Locale selection changes presentation only; it does not change verification,
proof search or Runtime ownership. Help documents the supported tokens; raw
terminal errors and the complete help prose are not localized by this change.
Maintained output uses exhaustive statement and rule explainers for all ten
languages.

Example command:

```sh
target/release/litex -lang ja -e '1 + 2 = 3'
```

The statement's Normal projection has the following fields (the CLI also
includes its run envelope):

```json
{
  "成功": true,
  "文": "1 + 2 = 3",
  "証明方法": {
    "型": "閉じた式の計算",
    "規則名": "閉じた式の計算",
    "説明": "閉じた式を正確に評価し、証明探索を行いません"
  },
  "保存": ["1 + 2 = 3"],
  "推論": []
}
```

Acceptance covers ten-language success/failure projections, readable citations,
field order and key collisions, positive/negative membership wording, all
statement/proof-route copy, and the existing equality-rule acceptance inventory.
Translations are authored technical copy; these checks establish coverage and
behavioral compatibility, not independent native-speaker linguistic review.

### Rule language method contract

Every builtin rule and rule-family explanation impl owns these public methods:
`rule_name_and_message_en`, `_zh`, `_zh_hant`, `_fr`, `_ru`, `_es`, `_ar`, `_ja`,
`_ko`, and `_vi`. Each method owns its locale's rule name and message. The
`rule_name_and_message(language)` API contains only an exhaustive
language selector calling those methods. Rule-family methods then dispatch to
the corresponding named methods on their payloads. Equality aggregate and
scalar copy also belongs to the payload's impl; the equality enum only routes
variants. No locale calls another locale's method.

`BuiltinRuleText` contains exactly `rule_name: String` and `message: String`.
The existing proof type or enum variant identifies the rule; localized copy
does not duplicate that identity in a string field. Atomic and equality
`text(...)` calls share the constructor in `explain/text.rs`, for example:

```rust
text(
    "arcsin与sin的逆运算复合",
    "在 [-π/2, π/2] 上，arcsin与sin复合后得到原参数，即 arcsin(sin(x)) = x",
)
```

The old ID-bearing methods and unused fallback/bilingual compatibility helpers
have been removed. Normal JSON still renders the same name and message.
Detailed proof serialization retains its independently consumed machine rule
tags and `rule_id()` methods.

For example, `PowerProductSameBaseBuiltinRuleProof` retains the equation
`a^m · a^n = a^(m+n)` in every locale, but also names and explains the rule in
that locale: Chinese says `同底数幂相乘` and explains that the exponents are
added; Japanese says `同じ底の累乗の積` and gives the same mathematical meaning.
The proof type identifies this rule. Formula notation alone is insufficient
for either the human-facing name or message.

`ArcsinExactZero` similarly names the value of the inverse sine at zero and
explains that the value is zero before giving `arcsin(0) = 0`. Keep identities,
domain restrictions, operand order, and positive/negative conclusions accurate
to the owning verifier rule. In particular, `SqrtSquare` describes squaring a
square root, `(sqrt(x))^2 = x` for nonnegative real `x`;
`IntersectSetMinusSelfEmpty` describes `A ∩ (B \ A) = ∅`; and
`ZeroFromNatAndOneLe` derives `n != 0` from `n $in N` and `1 <= n`.

`rule_language_methods_tests` audits every impl in the atomic/equality rule
explanation directories for this method contract and selector shape, and
checks the power-product method API directly. It also scans all maintained
literal builtin names/messages for human prose in the selected language,
matching each impl's locale branches with its English branches without string
rule IDs. This guards against formula-only copy and whole English sentences
in locales with different scripts; it is not a grammar checker. Semantic regression tests
cover the inverse-sine tracer, principal inverse interval, square-root and
set-difference identities, and natural-number nonzero conclusion.
The equality acceptance inventory
also compares each named method with the generic dispatcher across every
inventoried variant and all ten locales. Locale keys and non-builtin statement
explanations retain their existing interfaces.

The ID-removal acceptance on 2026-10-04 passed the release build, all 65 JSON
tests, and the existing `legacy_final_capabilities` explanation consumer test.
All 80 real CLI cases across ten languages (70 successes and 10 expected
failures) retained identical exits, stdout, and stderr. A source comparison
also preserved all 9,755 non-ID rule literals and rule dispatch logic while
removing 4,380 constructor ID arguments and 230 direct ID fields.

Detailed `FnApplicationInStandardSuperset` evidence records `target_set` and `signature_returns`. Each return entry carries `source_set`, `cite_signature_fact_id`, and the actual `function_equal` path. This certifies numeric set inclusion; it does not manufacture a return-set equality proof. The enclosing fact result owns the application WD and domain evidence.

Detailed `FnApplicationInCodomain` retains the selected signature citation and
its actual `function_equal` path. Each alternative has either a checked
`return_set_match` or `same_call_domains` evidence. The latter compares
parameters and guards separately at every actual call layer and retains
returned carrier equality paths; it allows different return upper bounds.
The enclosing application WD still checks the actual arguments. A cached call
through a broader signature does not establish a narrower signature's guard.
The `source_signature`, `target_signature`, `domain_comparison` and path keys
reuse the existing locale schema.

Detailed `HomogeneousTupleCoordinate` evidence records `shape` and one `carrier_equals` proof per Cartesian factor. The shape includes its stored membership/signature and carrier/subject equality provenance. The enclosing fact WD owns index positivity and the upper bound; the leaf only reads stored shape/equality facts.

Detailed `TupleIndexUpperBound` records `shape` and `source_bound`; the latter includes the stored inequality and its argument equality evidence. The read-only leaf transports a stored bound to the certified tuple dimension and retains both sources.

Detailed `ModNestedDivisibleAbsorption` records `proof_of_requirement_facts`,
including the actual multiplier-in-Z verification and stored citation when
applicable. Enclosing equality WD still owns integer/nonzero modulus evidence.
The [local guard regression](../../examples/proof_nodes/equal/by_builtin_rule/nested_mod_integer_multiple.lit)
checks fractional-multiplier rejection and preserves signed integer multiples.


Detailed atomic witness success projects the already checked predicate arguments,
projected existential, ambient WD/type results, local proof steps and body/unique
obligations in execution order. Nonempty witness failure projects exactly the
owned ObjWd, SetWd, ProofBody or Membership result; ProofBody retains its step
index. Neither exposes local_env. The [witness evidence tracer](../../examples/stmt_nodes/witness/witness_detailed_evidence.lit)
and [focused evidence note](../../examples/stmt_nodes/experience/problem_notes/witness-detailed-evidence-2026-10-05.md)
record the local consumer repair; execution and Normal contracts stay unchanged.


Detailed ProductComponentNonzero projects `product_nonzero_proof` from the
verifier-owned AtomicExceptEqualityFactKnownProof: its actual fact and selected
known-source searched proof. The [dedicated reflection tracer](../../examples/proof_nodes/atomic/by_builtin_rule/zero_nonzero_reflection_evidence.lit)
and [source evidence note](../../examples/proof_nodes/experience/problem_notes/zero-nonzero-reflection-2026-10-05.md)
record exact source-ID tests in English and Chinese. Normal projection and
locale key maps are unchanged; independent certificate replay is unverified.


Detailed `FactorialMonotone` projects the actual `argument_order` verification;
`FactorialStrictMonotone` projects `positive_smaller`, then `argument_order`
in producer order. Either order spelling retains its actual source citation.
The four new factorial/lcm typed winning leaves own ten language selectors.
`LcmLeftAbsDivisibility` and `LcmRightAbsDivisibility` are separate unconditional
identities under checked parent WD; no nonexistent source premise is projected.
The enclosing equality owns integer and nonzero-modulus evidence. Existing
`PositiveIntegerInNPos` retains `integer_proof` and the actual `positive_proof`
for either x>0 or 0<x; its payload and projector shape are unchanged.
The [leaf evidence record](../../examples/proof_nodes/experience/problem_notes/factorial-lcm-leaf-repair-2026-10-05.md)
links source-ID, permission, negative and selected consumer gates. Independent
certificate replay and Lean compilation remain outside this verification scope.


Exp/Ln strict/weak forward leaves project actual `argument_order` verification;
their order-reflection leaves project actual `image_order`, including its WD.
Eight typed owners supply ten localized name/guard-message selectors. Reverse
written source premises retain their real citations and inherited ceilings.
The [exp/ln consumer record](../../examples/proof_nodes/experience/problem_notes/exp-ln-order-repair-2026-10-05.md)
links current-source Detailed/language gates and the still-pending nested-ln
predicate-domain WD consumer. Warm ln-sign KnownEqualObjSubstitution consumes
a real earlier ln(1)=0 and the native order leaf; it is not a known-forall proof.
Independent certificate replay and Lean compilation are outside these gates.


LnAsEulerLog and ExpAsEulerIntegerPower each own ten guarded language texts and a separate Detailed identity leaf. They consume no searched premise and fabricate no child; enclosing equality retains actual exp/ln/log/power WD. The [fixed-base record](../../examples/proof_nodes/experience/problem_notes/fixed-base-bridge-repair-2026-10-05.md) links actual typed owner gates and valid prior-forall citations. Full release/Lean/replay remains outside this local contract gate.


The four rounding bounds and TanQuotientDefinition, CotQuotientDefinition and
GcdEuclideanStep each retain a distinct Detailed builtin leaf and ten localized
Normal explanations. Their enclosing verification retains the original object
WD guards. Structural finite-extremum membership uses intrinsic
`finite_set_max` / `finite_set_min` real codomains; `known_subset` retains both
actual `member_proof` and `subset_proof` citations. The
[source-owned acceptance record](../../examples/proof_nodes/experience/problem_notes/obj-definition-builtin-rules-2026-10-05.md)
checks the actual executed leaves through Detailed and Normal consumers. Normal
continues to summarize a whole forall with its compound proof label.


Detailed LogStrictDecreasing and LogWeakDecreasing each retain nested `guards` with four mandatory actual producer fields: `base_positive_proof`, `base_lt_one_proof`, `left_arg_positive_proof`, `right_arg_positive_proof`, followed by actual `argument_order`. Reverse written guards/comparisons cite the actual known facts. Two typed leaves own ten guarded localized outputs; existing increasing log paths remain first. [Source evidence](../../examples/proof_nodes/experience/problem_notes/log-unit-interval-order-repair-2026-10-05.md) records actual English/Chinese citations and selected language/Detailed gates; shared search ceilings and independent replay are not broadened.


FnRange WD and FnRangeOfEmptyDomain retain checked complete-domain sources.
FnRangeOfConstantAnonymousFn now retains an inhabited-domain certificate,
including actual argument memberships and guards. FunctionGraphNonemptyFromDomain
and FunctionSpaceNonemptyFromEmptyDomain describe graph values and function
spaces separately. Nested function-space existence keeps each return layer.
Detailed projection retains these certificates; both image leaves own ten
localized explanations and actual Runtime acceptance fixtures.

Nested existence certificates retain checked return-carrier transports and
each finite Cartesian factor. seq and finite_seq project their actual input
signature and constructive return witness. Closed integer range membership
projects the original range, exact scalar value and both endpoint values;
it keeps the existing closed-calculation route and localized keys.


CartMembership builtin and strategy evidence now retains the checked complete
function-domain match followed by each coordinate requirement proof. It no
longer substitutes an opaque shape/dimension marker for those children.
EmptyFunctionGraph retains its complete source and empty-domain certificate;
EmptyDomainFunctionSpaceSingleton retains the source space, exact signature
and empty-domain certificate. Both equality leaves own ten localized texts
and actual executed Runtime acceptance fixtures. Zero-factor Cartesian size
retains an empty list of factor-finiteness obligations: the empty product is
one, rather than an invented factor proof.

Guarded empty input domains use `checked_guard_input_exclusion` in Detailed
output. It retains the complete source signature, selected guard index and
checked typed-forall proof, including its FactId citation and local WD evidence.
The existing empty-carrier projection keeps its prior fields. Graph, image and
function-space consumers share this certificate; a search miss is not an
emptiness proof.

AnonymousFn WD projects its return-bound choice explicitly. A checked ordinary body membership retains its prior JSON route; an empty complete domain uses return_bound_vacuous_empty_domain with the independent domain_empty certificate. Header, guards, return carrier and body WD remain separate children. Ten-language Runtime tests preserve the guard-exclusion forall/FactId source and mandatory body WD rather than emitting a fake body membership.

The predicate-signature failure reason retired_builtin identifies a legacy shape predicate payload rejected by WD. It preserves the already-checked argument children and predicate name in all localized profiles; no unsupported predicate is published as a current builtin. Parser retirement remains a separate session_error boundary.
