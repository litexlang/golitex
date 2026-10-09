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
| [store_fact_and_infer/store_fact_and_infer_result/store_and_infer_result.rs](store_fact_and_infer/store_fact_and_infer_result/store_and_infer_result.rs) | `StoreFactAndInferResult` | The stored seed fact and forward consequences, represented as separate `store` and `infer` stages. |

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
| Atomic proof search | `AtomicFact`, `VerifyState`, searched-proof payloads | [verify_atomic_fact/search_atomic_fact.rs](execute/execute_fact_stmt/verify_atomic_fact/search_atomic_fact.rs): `search_atomic_fact`. Orders the available proof routes. [verify_state.rs](execute/execute_fact_stmt/verify_state.rs): `VerifyState::for_premises` limits which routes their premises may use. |
| Fact storage and inference | `KnownFactMemory`, `StoreFactAndInferResult` | [store_fact_and_infer.rs](store_fact_and_infer/store_fact_and_infer.rs): `store_fact_and_infer`; [store_fact.rs](store_fact_and_infer/store_fact.rs): `store_fact`; [infer_fact.rs](store_fact_and_infer/infer_fact/infer_fact.rs): `infer_fact`. Stores the seed, then dispatches its local forward consequences. |
| Structured proofs | `ClaimStmt`, `ForallFact`, local `ExecEnv` and proof results | [exec_claim_stmt.rs](execute/execute_proof_block_stmt/exec_claim_stmt.rs): `exec_claim_stmt`; [verify_forall_fact.rs](execute/execute_fact_stmt/verify_forall_fact/verify_forall_fact.rs): `verify_forall_fact`. Shows local parameters, premises and conclusion checking. A successful claim publishes its goal while retaining local evidence in its result. |

For the shortest algorithm route, follow `run_litex_code` → `exec_stmt` →
`execute_fact_statement` → `verify_fact`. Then inspect the chosen fact family,
`search_atomic_fact` for an atomic goal, and `store_fact_and_infer` after
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
   before proof search. `search_atomic_fact` selects a supported route under
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
| How do files and modules share knowledge? | [LitexConfig](module_manager/litex_config.rs), [GlobalModuleManager](module_manager/global_module_manager.rs), [ExportFileAndItsExecEnv](module_manager/export_file.rs) | [run_file_with_config](run_module/run_file_with_config.rs), [run_import_module](run_module/run_import_module.rs); [run_module guide](run_module/README.md) and [module manager guide](module_manager/README.md). Each completed export retains its own environment. |
| How are quantified facts instantiated? | [TypedParameterList](ast/param.rs), [BoundName](ast/names.rs), [Fact](ast/fact/fact.rs) | [instantiate/](instantiate/), plus [known-forall search](execute/execute_fact_stmt/verify_atomic_fact/search_proof_by_known_forall_fact.rs). |
| How do results become explanations? | `RunLitexCodeResult`, `ExecStmtResult`, `VerifyFactResult` | [json_output/emit.rs](json_output/emit.rs): `emit_run_normal`, `emit_run_detailed`; [JSON guide](json_output/README.md). |
| How are supported proofs replayed into Lean? | The same typed results, retained environments and cited IDs | [LitexToLeanCompiler](compile_to_lean/litex_to_lean_compiler.rs): `compile`; [compiler guide](compile_to_lean/README.md). Generation and independent Lean checking are separate steps, and replay supports a bounded subset. |
| How is mathematical source exported to LaTeX? | Parsed `Stmt`, `Fact` and `Obj` | [compile_to_latex/source.rs](compile_to_latex/source.rs): `to_latex`; [LaTeX guide](compile_to_latex/README.md). This path renders parsed source without verifying it. |
| How are computational fragments extracted? | [extract_executable_code/program.rs](extract_executable_code/program.rs) | [source_extraction.rs](extract_executable_code/source_extraction.rs): `extract_code_from_source`; [extraction guide](extract_executable_code/README.md). |
| How is checked module knowledge persisted? | [knowledge_base/](knowledge_base/) codecs for definitions and facts | [knowledge-base guide](knowledge_base/README.md), especially its import/cache compatibility boundary. |

[lib.rs](lib.rs) lists the wired Rust modules. When a type, dispatcher or
component ownership changes, update its row here alongside the owning
subsystem documentation.
