# Reading the Litex source

Start with the data structures, then follow the algorithms that construct,
check and store them. Litex represents mathematical objects, propositions and
actions separately. Execution can extend a scoped context and leaves typed
results describing a statement's verification and effects. Those
representations explain how later statements can use earlier knowledge.

This is the source-reading entrance for the current Rust kernel. The
[Manual](../docs/Manual.md) teaches the language; the subsystem READMEs linked
below explain individual components in more detail.

## Read the central data structures first

Read the declarations at the beginning of these files before their methods.
The order moves from what a statement means, to its context, to the evidence
left by processing it.

| Main file | Central types | What to understand |
| --- | --- | --- |
| [ast/obj.rs](ast/obj.rs) | `Obj` and its expression families | Mathematical values and expressions: names, numbers, sets, function applications and constructions. For example, `a + 1` is an object expression. |
| [ast/fact/fact.rs](ast/fact/fact.rs) | `Fact` | Propositions about objects: atomic facts, conjunctions, chains, disjunctions and quantifiers. `a + 1 = 3` is a fact. Follow [atomic.rs](ast/fact/atomic.rs) and [forall_fact.rs](ast/fact/forall_fact.rs) for their payloads. |
| [ast/stmt.rs](ast/stmt.rs) | `Stmt`, `DefinitionStmt`, `ByStmt`, `ProofBlockStmt` | Actions that assert facts, introduce definitions or perform proofs. `have a R = 2` is a definition action; a bare fact becomes `Stmt::Fact`. |
| [ast/names.rs](ast/names.rs), [ast/param.rs](ast/param.rs) | `BoundName`, `AtomicName`, `ParamType`, `TypedParameterList` | Binder identity, qualified names and parameter domains. Names and bound parameters have identities beyond their displayed spelling; see [identifier_identity.md](identifier_identity.md). |
| [runtime/runtime.rs](runtime/runtime.rs) | `Runtime`, `ParseScope`, `GlobalIds` | The live session: parse and execution scope stacks, current source, ID allocation and module state. |
| [exec_env/exec_env.rs](exec_env/exec_env.rs) | `ExecEnv`, `DefinitionMemory`, `WellDefinedObjectMemory` | One scope's definitions, facts, registered properties and object well-definedness records. A child can read its parents and writes into its own environment. |
| [exec_env/known_fact_memory.rs](exec_env/known_fact_memory.rs) | `KnownFactMemory`, `KnownEquivalenceClassMemory` | Stored facts by `FactId`, plus indexes for equality, atomic facts and quantified conclusions. Equality classes aid lookup; their generating equality edges retain the facts that justify a path. |
| [execute/exec_stmt_result.rs](execute/exec_stmt_result.rs) | `ExecStmtResult` | The statement-shaped result tree: what execution did and which nested result belongs to that action. |
| [execute/execute_fact_stmt/verify_fact_result.rs](execute/execute_fact_stmt/verify_fact_result.rs) | `VerifyFactResult` | The proposition-shaped verification tree. Follow a branch to see well-definedness evidence, its successful proof route or its failure. |
| [store_fact_and_infer/store_fact_and_infer_result/store_and_infer_result.rs](store_fact_and_infer/store_fact_and_infer_result/store_and_infer_result.rs) | `StoreFactAndInferResult` | Ordered stages: `store`, `formed_subjects` (new atomic-argument WD registrations), and optional `infer`. The latter is absent in store-only formation scopes. |

The source AST describes what was written. `ExecEnv` holds the knowledge
available in a scope. The result tree describes how a statement was processed.
Keep these roles distinct when reading an algorithm.

The connection is visible in this complete declaration from
[execute_fact_stmt/result.rs](execute/execute_fact_stmt/result.rs):

```rust
pub struct ExecFactStmtSuccessResult {
    pub verify_result: VerifyFactResult,
    pub store_and_infer_result: StoreFactAndInferResult,
}
```

The first field explains the grounds for accepting the fact; the second
explains what was stored and inferred. Result nodes can cite `FactId` or
`WellDefinednessId`, so understanding a result also requires the corresponding
environment. Some scoped proof results retain their local `ExecEnv` for that
purpose. [runtime_ids.rs](runtime/runtime_ids.rs) defines the identity types.

Acceptance can include explicit assumptions such as `trust` or `axiom`.
Use the [Manual's trust boundary](../docs/Manual.md#trust-and-strict-mode) when
interpreting what an accepted result establishes.

## Then read the component algorithms

Each row pairs a component's data with its main algorithm entry. These are
navigation points into the large components; individual mathematical rules
live below their dispatchers.

| Component | Data to keep in view | Main file and function |
| --- | --- | --- |
| Source execution | `Runtime`, `RunLitexCodeResult` | [run/run_litex_code.rs](run/run_litex_code.rs): `run_litex_code`, `parse_and_exec_token_block`. Connects tokenization, one statement's parsing and execution, and its result. [run_command_outcome.rs](run/run_command_outcome.rs) defines the run result. |
| Tokenization | `TokenBlock` | [tokenize/tokenizer.rs](tokenize/tokenizer.rs): `Tokenizer::tokenize`. Builds indented source blocks; [token_block.rs](tokenize/token_block.rs) defines their header, body and source location. |
| Parsing | `TokenBlock`, `Stmt`, `ParseScope` | [parse/parse.rs](parse/parse.rs): `parse_token_block`. Dispatches by the leading token. [fact.rs](parse/fact.rs) and [object/expression.rs](parse/object/expression.rs) parse the contained propositions and expressions. |
| Statement execution | `Stmt`, `ExecEnv`, `ExecStmtResult` | [execute/exec_stmt.rs](execute/exec_stmt.rs): `exec_stmt`, `exec_stmt_in_current_env`. Executes in a temporary environment and merges it into the parent only after success. |
| Fact-statement execution | `Fact`, `ExecFactStmtResult` | [execute_fact_stmt/exec_fact_stmt.rs](execute/execute_fact_stmt/exec_fact_stmt.rs): `execute_fact_statement`. Verifies a fact before storing it and running inference. |
| Well-definedness | `Obj`, `VerifyObjWellDefinedResult` | [well_defined_results/verify_obj/entry.rs](execute/execute_fact_stmt/well_defined_results/verify_obj/entry.rs): `verify_obj_well_definedness`. Checks whether an expression is meaningful under its domain conditions. Fact families also check predicate and binder requirements. |
| Fact verification | `Fact`, `VerifyFactResult` | [execute_fact_stmt/verify.rs](execute/execute_fact_stmt/verify.rs): `verify_fact`. Dispatches by logical shape. [verify_equal_fact.rs](execute/execute_fact_stmt/verify_atomic_fact/verify_equality/verify_equal_fact.rs): `verify_equal_fact` shows the well-definedness-then-proof pipeline for equality. |
| Atomic proof search | `EqualFact` or other `AtomicFact`, `VerifyState`, family searched-proof payloads | [search_equal_fact_proof.rs](execute/execute_fact_stmt/verify_atomic_fact/verify_equality/search_equal_fact_proof.rs) and [search_atomic_except_equality_fact_proof.rs](execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/search_atomic_except_equality_fact_proof.rs) own the two search pipelines. [verify_state.rs](execute/execute_fact_stmt/verify_state.rs): `VerifyState::for_premises` limits which routes their premises may use. |
| Fact storage and inference | `KnownFactMemory`, `StoreFactAndInferResult` | [store_fact_and_infer.rs](store_fact_and_infer/store_fact_and_infer.rs): `store_fact_and_infer`; [store_fact.rs](store_fact_and_infer/store_fact.rs): `store_fact`; [infer_fact.rs](store_fact_and_infer/infer_fact/infer_fact.rs): `infer_fact`. Stores the seed, then dispatches its direct forward consequences. Derived facts use a named rule certificate followed by store only; they do not reenter this dispatcher. |
| Structured proofs | `ClaimStmt`, `ForallFact`, local `ExecEnv` and proof results | [exec_claim_stmt.rs](execute/execute_proof_block_stmt/exec_claim_stmt.rs): `exec_claim_stmt`; [verify_forall_fact.rs](execute/execute_fact_stmt/verify_forall_fact/verify_forall_fact.rs): `verify_forall_fact`. Shows local parameters, premises and conclusion checking. A successful claim publishes its goal while retaining local evidence in its result. |

For the shortest algorithm route, follow `run_litex_code` → `exec_stmt` →
`execute_fact_statement` → `verify_fact`. Then inspect the chosen fact family,
`search_equal_fact_proof` or `search_atomic_except_equality_fact_proof` for an
atomic goal, and `store_fact_and_infer` after
success. Parsing happens before execution of each complete top-level block.

## Follow one fact through the representations

Trace the homepage's `a + 1 = 3` after `have a R = 2`:

1. **Meaning:** `Obj` represents `a + 1` and `3`; an `EqualFact` relates them;
   `Stmt::Fact` asks the session to establish that proposition.
2. **Available context:** `ExecEnv` holds the definition of `a` and stored
   facts including its membership and equality. `KnownFactMemory` provides
   the fact table and lookup indexes used by later verification.
3. **Execution boundary:** `exec_stmt` opens a temporary child environment;
   `execute_fact_statement` asks `verify_fact` to verify the proposition.
4. **Mathematical grounds:** the equality family checks well-definedness
   before proof search. `search_equal_fact_proof` selects a supported route under
   `VerifyState`; its searched-proof payload records that selected route.
5. **Knowledge produced:** on verification success, `store_fact_and_infer`
   records the equality and any supported forward consequences. The result
   pairs the verification evidence with these storage and inference effects.
6. **Next statement:** successful execution merges the child into its parent;
   the source runner commits its temporary parse bindings. An ordinary failed
   statement discards its tentative changes and leaves earlier accepted
   statements available. A multi-statement input is not one transaction.

This walkthrough follows the source owners; it does not prescribe a particular
winning arithmetic proof route. Inspect the actual typed result or Detailed
JSON when the exact route matters. See the [fact verifier guide](execute/execute_fact_stmt/README.md)
and [execution guide](execute/README.md) for evidence contracts.

## Expand into the surrounding components

Once the central model is clear, choose the component matching your question:

| Question | Data first | Algorithm and guide |
| --- | --- | --- |
| How does a tuple coordinate discard a zero summand? | [Zero-addition premise evidence](execute/execute_fact_stmt/verify_atomic_fact/verify_equality/verify_equality_by_builtin_rules/add_zero_from_equalities_builtin_rule_proof.rs) and the coordinate's closed numeric membership | [Checked-zero addition](execute/execute_fact_stmt/verify_atomic_fact/verify_equality/verify_equality_by_builtin_rules/search_add_zero_from_equalities.rs) checks both equalities; [literal coordinate reading](execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/known_literal_tuple_numeric_coordinate.rs) supplies numeric WD evidence without new search. [Plane identity tracer](../examples/proof_nodes/equal/by_builtin_rule/add_zero_from_equalities.lit). |
| How do files and modules share knowledge? | [LitexConfig](module_manager/litex_config.rs), [GlobalModuleManager](module_manager/global_module_manager.rs), [ExportFileAndItsExecEnv](module_manager/export_file.rs) | [run_file_with_config](run_module/run_file_with_config.rs), [run_import_module](run_module/run_import_module.rs); [run_module guide](run_module/README.md) and [module manager guide](module_manager/README.md). Each completed export retains its own environment. |
| How are quantified facts instantiated? | [TypedParameterList](ast/param.rs), [BoundName](ast/names.rs), [Fact](ast/fact/fact.rs) | [instantiate/](instantiate/), plus [known-forall search](execute/execute_fact_stmt/verify_atomic_fact/search_proof_by_known_forall_fact.rs). |
| How do results become explanations? | `RunLitexCodeResult`, `ExecStmtResult`, `VerifyFactResult` | [json_output/emit.rs](json_output/emit.rs): `emit_run_normal`, `emit_run_detailed`; [JSON guide](json_output/README.md). |
| How does interactive textbook reading work? | Versioned reading JSON: actual typed evidence, scoped facts, inference outputs, symbol identities and source ranges | [Reading subsystem](reading/README.md), [integration guide](../docs/reading.md) and [design](reading/DESIGN.md). `-reading` provides local import/preview, JSON and static export; the same viewer mounts in a website or iframe. |
| How are supported proofs replayed into Lean? | The same typed results, retained environments and cited IDs | [LitexToLeanCompiler](compile_to_lean/litex_to_lean_compiler.rs): `compile_run`; [compiler guide](compile_to_lean/README.md). Generation and independent Lean checking are separate steps, and replay supports a bounded subset. |
| How is mathematical source exported to LaTeX? | Parsed `Stmt`, `Fact` and `Obj` | [compile_to_latex/source.rs](compile_to_latex/source.rs): `to_latex`; [LaTeX guide](compile_to_latex/README.md). This path renders parsed source without verifying it. |
| How are computational fragments extracted? | [extract_executable_code/program.rs](extract_executable_code/program.rs) | [source_extraction.rs](extract_executable_code/source_extraction.rs): `extract_code_from_source`; [extraction guide](extract_executable_code/README.md). |
| How is checked module knowledge persisted? | [knowledge_base/](knowledge_base/) codecs for definitions and facts | [knowledge-base guide](knowledge_base/README.md), especially its import/cache compatibility boundary. |

## Points that look like bugs but are not

The kernel contains deliberate defenses that are easy to misread as defects.
Each row below names the suspicious behavior, the mechanism that makes it
intentional, and the file holding the actual code. The one genuine gap is
called out at the end.

### Identity and naming

| Looks suspicious | Why it is not a bug | Where |
| --- | --- | --- |
| `ir()` once collapsed `(a^b)^c` and `a^(b^c)` (and `-(a^b)` vs `(-a)^b`, `(a%b)%c` vs `a%(b%c)`) | `fmt_obj` now fully parenthesizes every arithmetic constructor, so `ir()` is injective by construction. | [display_and_ir/obj.rs](display_and_ir/obj.rs) |
| `Number(-5).ir()` equals `Neg(5).ir()` (both `"(-5)"`) | Intentional normalization: a generated negative literal and a parsed unary minus denote the same number. | [display_and_ir/obj.rs](display_and_ir/obj.rs) |
| Same-name binders are rejected instead of shadowed | A parse-time occupy fence forbids nested/shadowing reuse; this is deliberate, not an oversight. | [identifier_identity.md](identifier_identity.md) |
| A name-identical but id-different binder is rejected on lookup | `stored_identifier_definition_visible` compares `IdentifierId`, so a local same-name binder never captures an outer binding. | [execute/env_stack_lookup.rs](execute/env_stack_lookup.rs) |
| The same name may reappear in sibling scopes | Each binding gets a fresh monotonic `IdentifierId`; identity is id-based, not spelling-based. | [runtime/runtime_ids.rs](runtime/runtime_ids.rs) |
| Merging a child env that re-defines a name raises `InternalBug` | Defense in depth: the parse fence makes the collision unreachable on the success path. | [exec_env/merge_exec_env.rs](exec_env/merge_exec_env.rs) |
| Generated Lean names (`h_N`, `_object_iN`, `_value_iN`, `_Host_iN`) look collision-prone | All names are derived from distinct `FactId`/`IdentifierId` with separated prefixes; user source names never enter the Lean namespace. | [compile_to_lean/names.rs](compile_to_lean/names.rs) |

### Free parameters and substitution

| Looks suspicious | Why it is not a bug | Where |
| --- | --- | --- |
| A rigid subterm demands whole-value equality before constructor descent | `free.is_disjoint(param_set)` routes param-free patterns to strict equality first; only free params may bind. | [match_forall_conclusion_args.rs](execute/execute_fact_stmt/verify_atomic_fact/match_forall_conclusion_args.rs) |
| Substitution removes a binder from the map before entering its body | `shadow_binder_ids` implements capture avoidance; unique ids make it safe. | [instantiate/capture.rs](instantiate/capture.rs) |
| Builder/function signature matching rejects a substitution that mentions a local binder | The closing `subst.values()` check blocks local-binder capture. | [match_forall_conclusion_args.rs](execute/execute_fact_stmt/verify_atomic_fact/match_forall_conclusion_args.rs) |
| Dom-only middle parameters are completed by scanning known atomics | `complete_forall_subst_with_equality` requires each round to add bindings (`trial.len() > subst.len()`), so it cannot invent witnesses. | [match_forall_conclusion_args.rs](execute/execute_fact_stmt/verify_atomic_fact/match_forall_conclusion_args.rs) |
| A parameter bound twice may fail even if each side alone matches | `try_bind_forall_param`'s rebound branch requires the previous binding to equal the new one. | [match_forall_conclusion_args.rs](execute/execute_fact_stmt/verify_atomic_fact/match_forall_conclusion_args.rs) |

### Indexes and lookup

| Looks suspicious | Why it is not a bug | Where |
| --- | --- | --- |
| Shape-only index keys omit arguments and look "too coarse" | Keys only bucket candidates; the real match is a separate full alpha-equality / parameter match. | [or_fact_index_key.rs](exec_env/or_fact_index_key.rs), [exist_shaped_fact_index_key.rs](exec_env/exist_shaped_fact_index_key.rs), [forall_conclusion_index_key.rs](exec_env/forall_conclusion_index_key.rs) |
| Equivalence classes are keyed by `ObjIR` | Safe because `ir()` is injective; the generating `EqualFact`s remain in `facts_by_id` for evidence. | [known_fact_memory.rs](exec_env/known_fact_memory.rs) |
| `known_closed_numeric_equal` indexes only when exactly one side is closed | Both-closed and neither-closed equalities are deliberately skipped to avoid wrong representatives. | [known_fact_memory.rs](exec_env/known_fact_memory.rs) |
| `predicates_share_visible_definition` uses `std::ptr::eq` | Identity belongs to the visible declaration object, never to a printed name or equal clauses. | [env_stack_lookup.rs](execute/env_stack_lookup.rs) |
| A qualified name can fall back to the live stack | `lookup_named_definition` checks the finished export first and only falls back while that exact source is live. | [env_stack_lookup.rs](execute/env_stack_lookup.rs) |

### Alpha-equality

| Looks suspicious | Why it is not a bug | Where |
| --- | --- | --- |
| A free identifier never matches a bound identifier | `plain_ids_alpha_equal` requires exact id equality plus `map.values()` exclusion. | [by_they_are_the_same/helper.rs](execute/execute_fact_stmt/verify_atomic_fact/verify_equality/by_they_are_the_same/helper.rs) |
| Alpha-equality rejects two binders with the same target id | `extend_binder_map` refuses shadowed binders; incomplete, but never unsound. | [by_they_are_the_same/helper.rs](execute/execute_fact_stmt/verify_atomic_fact/verify_equality/by_they_are_the_same/helper.rs) |

### Numeric normalization

| Looks suspicious | Why it is not a bug | Where |
| --- | --- | --- |
| `-0` becomes `0`, `5.0` becomes `5` | `normalize_decimal_number_string` produces one canonical spelling per value. | [rational_expression/decimal_arithmetic.rs](rational_expression/decimal_arithmetic.rs) |
| Negative `mod`/`quot`/`floor`/`ceil` look arbitrary | They use the floor convention, applied consistently across evaluation and order rules. | [rational_expression/decimal_arithmetic.rs](rational_expression/decimal_arithmetic.rs) |
| `0^0 = 1` | The natural-power convention used by the power-law rules. | [by_power_laws.rs](execute/execute_fact_stmt/verify_atomic_fact/verify_equality/verify_equality_by_builtin_rules/by_power_laws.rs) |

### Execution boundary and merge

| Looks suspicious | Why it is not a bug | Where |
| --- | --- | --- |
| A failed statement might pollute the session | Each statement runs in a temp child env; only success merges it into the parent. | [exec_stmt.rs](execute/exec_stmt.rs), [merge_exec_env.rs](exec_env/merge_exec_env.rs) |
| `session_view` could be copied into child scopes | It is never merged; only the file-level env owns it. | [merge_exec_env.rs](exec_env/merge_exec_env.rs) |

### Lean compiler

| Looks suspicious | Why it is not a bug | Where |
| --- | --- | --- |
| Many proof routes return `LeanCompileError::unsupported` | The compiler is deliberately conservative: it fails instead of emitting Lean it cannot justify (incomplete, not unsound). | [compile_to_lean/](compile_to_lean/) |
| Compiled output seems to trust the result tree | `validate_statement_capture` / `instantiated_object_matches` reject any source-vs-result mismatch before emission. | [compile_to_lean/helper.rs](compile_to_lean/helper.rs) |

### Known genuine gap

- Generated Lean is compared as text against golden files in `cargo test`; it is
  **not** type-checked against the Lean kernel there. Lean-kernel acceptance is a
  separate Mathlib + `lake` step. See
  [tests/unit/run/lean_command/README.md](../tests/unit/run/lean_command/README.md).

[lib.rs](lib.rs) lists the wired Rust modules. When a type, dispatcher or
component ownership changes, update its row here alongside the owning
subsystem documentation.
