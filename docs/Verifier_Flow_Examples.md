# Verifier Flow Examples

Jiachen Shen and The Litex Team, 2026-06-01. Email: litexlang@outlook.com

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Verifier_Flow_Examples.md


## Purpose

This page explains the verifier flow with small Litex shapes and the main Rust
entrypoints they exercise.

The examples below are short shapes, not all standalone files. They are meant to
show which part of the executor or verifier is active. For runnable syntax
examples, read the [Manual](https://litexlang.com/doc/Manual).

## How To Read The Split

Litex statements do not all ask the verifier the same question.

- **Ordinary executor statements** such as `prop`, `have`, `eval`, `import`,
  `run_file`, `by thm`, `witness`, and the outer `claim`/`thm`/`strategy`
  statements are executed by `Runtime::exec_stmt` or the global statement
  runner. They may define names, open local environments, run nested
  statements, store declarations, or generate proof obligations.
- **Proof-required factual statements** such as a bare fact, a claim goal, a
  theorem body obligation, a witness obligation, or an algorithm coverage fact
  must be closed by the fact verifier. These paths use
  `verify_fact_return_err_if_not_true`, `verify_fact`, `verify_atomic_fact`, or
  a shape-specific `verify_*` function. If the result is `StmtUnknown`, the
  caller usually reports a failed proof step.
- **Store/assume statements** such as `know`, `let` facts, and domain facts
  assumed while checking a `forall` first check well-definedness, then store the
  fact and run inference. They are useful context-building tools, but they are
  not proof routes.

## Flow Examples

| Flow node | Litex shape | Main Rust path | What happens |
|-----------|-------------|----------------|--------------|
| Source input | A `.lit` file, `-e` code, `import Nat`, or `run_file "./x.lit"` | `run_source_code_in_file`, `run_source_code`, `Runtime::new_with_builtin_code`, `Runtime::new_for_import_from_parent`, `run_stmt_at_global_env` | A top-level run creates a runtime with builtin code; imported-module runtimes share the parent module manager. Litex tokenizes the input and executes statements in order. |
| Block parsing | `claim 3 = 3:` followed by indented proof lines | `Tokenizer::parse_blocks`, then `Runtime::parse_stmt` | The tokenizer preserves nested blocks so parser functions can build one `Stmt` with its body. |
| Global statement runner | `import Nat` or `run_file "./x.lit"` | `run_stmt_at_global_env` | `import` and `run_file` are special-cased before ordinary `exec_stmt`; other statements go directly to `Runtime::exec_stmt`. |
| Statement dispatch | A bare fact `1 + 1 = 2`, a `know` block, or a `thm` block | `Runtime::exec_stmt` | The runtime matches the `Stmt` variant and calls the corresponding `exec_*` function. |
| Non-factual executor | `prop p(x R): x = x`, `have x R`, `have fn f(x R) R = x + 1` | `exec_def_prop_stmt`, `exec_have_obj_in_nonempty_set_or_param_type_stmt`, `exec_have_fn_equal_stmt` | These statements define names, check well-definedness or type conditions, store declarations, and return `NonFactualStmtSuccess`. |
| Proof/control executor | `claim 3 = 3: 3 = 3`, `thm T: ...`, `prove: ...`, `by cases`, `by induc`, `by zorn_lemma`, `witness ...` | `exec_claim_stmt`, `exec_def_thm_stmt`, `exec_prove_stmt`, `execute/by_stmt/*`, `exec_witness_stmt` | The executor usually opens a local environment, recursively runs nested statements, and then checks generated goals or then-clauses. |
| Proof-required obligation | A bare fact `1 + 1 = 2`, a claim goal, a theorem then-clause, or an algorithm coverage fact | `exec_fact`, `verify_fact_return_err_if_not_true`, `verify_fact`, `verify_atomic_fact` | The verifier must return true. If the result is `StmtUnknown`, callers such as `exec_fact`, `claim`, or `thm` turn that into a verification failure. |
| Store/assume-only path | `know x = 2`; `let a R: a = 1`; a `forall` domain fact assumed inside a local proof | `exec_know_stmt`, `exec_let_stmt`, `verify_fact_well_defined_and_store_and_infer`, `verify_well_defined_and_store_and_infer`, `store_*_without_well_defined_verified_and_infer` | Litex checks that the fact is meaningful and stores it as context. This is not a proof route; it is trusted input, local assumption, or caller-checked context. |
| Fact dispatch | `x = y`, `x $in R`, `1 < 2 and 2 < 3`, `1 <= 2 = 2 < 3`, `exist x R st {x = 0}`, `forall! x R: x = x` | `verify_fact` | The verifier dispatches by fact shape: atomic, conjunction, chain, disjunction, existence, universal fact, universal iff fact, or negated universal fact. |
| Well-definedness | `1 / 0 = 0`, `f(1) = 2` when `1` is outside the domain, or an undeclared name | `verify_fact_well_defined`, `verify_obj_well_defined_and_store_cache` | Before proof search, Litex checks scope, object validity, predicates, function domains, and meaningful operations. Failure is an error, not `unknown`. |
| Equality proof routes | `2 + 3 = 5`, `a = 1` after `have a R = 1`, or `f(x) = x + 1` after `have fn f(x R) R = x + 1` | `verify_equal_fact`, `verify_objs_are_equal`, equality builtin and known-equality helpers | Equality tries builtin rules, known-only/equality cache, known equalities, definition substitution, same-shape recursive equality, function equality, and known `forall` matching. |
| Predicate proof routes | `2 $in R`, `$p(1)` after `prop p(x R): x = x`, or `$p(a)` after a stored `forall` fact | `verify_non_equational_atomic_fact` | Predicate facts try builtin rules, known atomic facts, prop definitions, known `forall` facts, active strategies, and relation-property post-processing. |
| Compound fact handling | `1 < 2 and 2 < 3`; `1 <= 2 = 2 < 3`; `A or B`; `exist x R st {x = 0}` | `verify_and_fact`, `verify_chain_fact`, `verify_or_fact`, `verify_exist_fact` | Compound verifiers first check well-definedness and then reduce the goal into smaller atomic or branch/witness obligations. |
| Universal fact handling | `forall! x R: x = x`; a `thm` or `claim forall ...` | `verify_forall_fact`, `forall_assume_params_and_dom_in_current_env`, `forall_verify_then_facts_in_current_env` | Litex opens a local environment, binds universal parameters, assumes domain facts, verifies then-facts, and returns a factual success only if the body is checked. |
| Theorem use | `by thm T(a)` | `exec_by_thm_stmt` | Litex looks up the theorem, checks argument types and domain facts, instantiates theorem conclusions, and stores the instantiated then-facts. |
| Strategy use | `strategy S: ...`, then `use strategy S` | `exec_def_strategy_stmt`, `exec_use_strategy_stmt`, `verify_non_equational_atomic_fact_with_strategy` | A strategy is first checked like a theorem-shaped proof. When activated, it becomes a proof route for matching atomic predicate goals. |
| Storage and indexing | Storing `a = 1`, a chain such as `a < b < c`, or a `forall` fact | `store_and_infer_fact_without_well_defined_verified`, `store_whole_fact_update_cache_known_fact_and_infer`, `store_atomic_fact_without_well_defined_verified_and_infer`, `store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer` | Accepted facts enter the environment, known-fact cache, equality/forall lookup structures, and chain/transitive-closure caches where applicable. |
| Builtin inference | After storing `have x R`, `x = 1`, or a set/membership fact | `Runtime::infer`, `infer_atomic_fact`, `infer_equal_fact`, `infer_in_fact`, and related infer helpers | Inference adds routine consequences such as domain facts, memberships, equalities, order consequences, and function facts so later statements can use them. |
| Factual success output | A verified bare fact such as `1 + 1 = 2` | `FactualStmtSuccess` | Output can include the fact, `verified_by`, and inferred facts. This is the result shape for a fact that Litex proved. |
| Non-factual success output | `have x R`, `claim ...`, `by thm T(a)`, or `know ...` | `NonFactualStmtSuccess` | Output can include the executed statement, nested `inside_results`, and `infer_facts`. It does not necessarily mean the statement itself is a factual proof. |
| Unknown output | A meaningful but unproved bare fact, such as a predicate fact with no known rule or assumption | `StmtUnknown` | `unknown` means the fact is well-defined but no proof route closed it. Top-level bare facts and proof obligations usually turn this into a failed run. |
| Error output | Bad syntax, undeclared names, invalid domains, `1 / 0`, or a proof block whose required step is unknown | `RuntimeError`, `VerifyRuntimeError`, `StoreFactRuntimeError`, `UnknownRuntimeError` | Errors stop execution and are reported with the statement, cause, and any nested results accumulated before the failure. |

## Boundary Examples

| Boundary item | Example | Why it is trusted |
|---------------|---------|-------------------|
| Parser and block structure | A `claim` block must attach the right indented proof lines to the right statement. | If parsing is wrong, the verifier may check a different statement from the one the user intended. |
| Well-definedness checker | `f(x)` should only be meaningful when `x` satisfies the function domain. | Litex relies on well-definedness before deciding whether a fact is true, unknown, or invalid. |
| Builtin verification rules | Arithmetic can close `2 + 3 = 5`; membership rules can close ordinary set facts. | These rules are implementation logic rather than user-provided proof terms. |
| Store and indexing logic | A stored chain may add adjacent and transitive consequences to caches. | Later proof search relies on the indexed context being faithful to accepted facts. |
| Builtin inference | Storing a domain or equality fact may add routine consequences. | Inferred facts become available to later statements, so inference rules are part of the trusted base. |
| Explicit assumptions | `know x = 2` and some `let`/domain assumptions can enter context without a proof route. | This is useful for axioms and proof debt, but later results can depend on it. |

The important reading discipline is: **proved facts**, **non-factual executor
success**, and **stored assumptions** are different things. Litex's output is
structured to keep that distinction visible.
