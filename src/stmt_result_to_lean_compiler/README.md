# Turn Litex Kernel Execution Information into Lean Proofs

## Start with one checked path

The Litex example `2 * i + 1 = i * i + 2 + 2 * i` records `ComplexAlgebraicNormalization` evidence and compiles that exact route into Lean code.

```text
verified Litex StmtResult
  -> validate the recorded target and child Results
  -> represent each Litex object with its Lean carrier/evidence contract
  -> compile the recorded proof constructor
  -> emit Lean declarations in source order
  -> fail closed on an unsupported Result instead of emitting `sorry`
```

The runnable pair is [`lean/examples/54_ComplexAlgebraicCalculation.lit`](../../lean/examples/54_ComplexAlgebraicCalculation.lit) plus its generated Lean check; the nearby boundary is the same division example without `z + i != 0`.

## The Two Hard Problems in the StmtResult-to-Lean Compiler

1. *Represent Litex mathematics in Lean, which is a theoretical problem.* The compiler must choose a representation for each mathematical concept that is consistent with Lean and Mathlib, and that will remain natural and usable in ordinary Lean developments.

The same mathematical object or statement can often be written in Lean in
several different ways. Although these representations may express the same
mathematics, choosing one of them is a long-term compiler decision: it affects
which Lean and Mathlib theorems generated code can reuse, how later Litex
features can be added, and how well the Litex and Lean ecosystems can work
together.

The most important decisions concern basic concepts such as functions, sets,
membership, and well-definedness. Litex and Lean handle these concepts in
fundamentally different ways. The compiler therefore needs a consistent
translation model for each of them. Its goal is not merely to produce Lean
code that passes today's examples, but to produce Lean representations that
remain natural and usable in ordinary Lean developments.

2. *Turn Litex kernel execution information into Lean proofs, which is a practical problem.* The Litex kernel reads what you want to prove and searches for a proof. The compiler must translate that search into Lean code, so that Lean can check the proof and use it in later developments.

The compiler must preserve the successful route of Litex verification as structured proof information and translate it into Lean code, without reconstructing the proof from display text or asking Lean to search for a different proof.

Litex verifies a formula by searching a tree. It repeatedly breaks the goal
into smaller goals and explores possible branches. When a branch succeeds,
the reason it succeeded must be returned from the leaves of the tree back to
the root. That returned information must describe which rules were used,
which facts and mathematical objects were involved, how each subgoal was
proved, and which well-definedness results were required.

The compiler must preserve this successful route as structured proof
information and translate it into Lean code. It should not reconstruct the
proof from display text or ask Lean to search for a different proof.

Litex statements return information in a similar way. As a statement is
executed, nested operations may introduce declarations, construct objects,
store facts, establish well-definedness, or change the local environment.
Those results also need to be returned compositionally and recorded with the
proof information.

The central compiler problem is therefore to design one precise structure for
the information returned by successful verification and statement execution,
and then translate that structure deterministically into Lean declarations
and proof terms.

The following sections describe the compiler's design for these two problems. 

## Representation of Litex Mathematics in Lean

## System-Wide Implicit Host-Type Convention

Status: confirmed on 2026-08-21; this is the target ABI used by the direct
StmtResult-to-Lean compiler.

**System-wide invariant:** every Lean type parameter introduced solely to host
a Litex source value must be implicit. This applies recursively throughout the
compiler ABI: top-level and nested `forall` binders, named and anonymous
function inputs, predicate and theorem inputs, dependent binder scopes, and
every other source-value input position. Each independently bound source value
gets its own inferred carrier unless the source evidence explicitly establishes
a shared representation. Generated source must use `{alpha : Type}` rather
than `(alpha : Type)`, and the carrier argument must never become part of the
Litex-facing call syntax.

This convention does not claim that generated Lean terms are untyped. It
separates host typing from Litex mathematical classification: Lean still checks
every term against a concrete or inferred host type, while Litex set membership
is represented only by explicit `Litex.In` evidence. A compiler-owned value
that already inhabits an exact `S.Carrier` needs no additional host-type
parameter, so exact-carrier outputs and fixed Mathlib constants do not violate
the invariant.

Every Litex input-value binder must use its own implicit Lean host carrier.
The host type represents and transports the source value but carries no Litex
mathematical classification. For example, the target shape of:

```litex
forall a R, b C:
    a + b = b + a
```

is:

```lean
∀ {α β : Type}
  (a : α) (haR : Litex.In a Litex.R)
  (b : β) (hbC : Litex.In b Litex.C),
  Litex.Same
    ((Litex.In.rep a haR : ℝ) + (Litex.In.rep b hbC : ℂ))
    ((Litex.In.rep b hbC : ℂ) + (Litex.In.rep a haR : ℝ))
```

Thus Lean typing is the host representation layer, `Litex.In` is the source
mathematical-classification layer, and `Litex.In.rep` is the proved route from
one visible membership fact to the exact native carrier required by an
operation. Proving another membership for `a` never changes `α`; it supplies
another independently usable representative. The compiler must select the
membership FactId retained for the exact source occurrence and must fail
closed when the required membership evidence is absent.

The policy does not hide Litex set parameters, erase the fixed Mathlib carriers
of native constants, or re-box compiler results that already inhabit an exact
`S.Carrier`. Existential and `have` outputs may use the exact carrier of the set
from which the compiler constructs their representative; they introduce no
separate explicit host-type parameter. In short:

```text
input value  = implicit host carrier + explicit Litex.In evidence
output value = exact target-set carrier
operation    = verifier-selected evidence + Litex.In.rep
```

Nearest rejected forms are binding `forall a R` directly as `a : ℝ`, binding
all standard numeric inputs as `a : ℂ`, or choosing a representative from an
unrelated membership merely because it elaborates to the desired Lean type.

When a verifier-selected membership proof supplies an exact real
representative and the surrounding native arithmetic expression unambiguously
has carrier `ℂ`, generated Lean should rely on Lean's standard `ℝ → ℂ`
coercion instead of printing a redundant explicit outer cast. The preferred
surface form is:

```lean
(Litex.In.rep a haR : ℝ) + (Litex.In.rep b hbC : ℂ)
```

rather than:

```lean
((Litex.In.rep a haR : ℝ) : ℂ) + (Litex.In.rep b hbC : ℂ)
```

This is only a generated-source readability decision. The recursive Result
and compiler representation bindings must still retain that
`haR : Litex.In a Litex.R` first selects an
exact `ℝ` representative and that Lean then embeds that value into `ℂ` for
the addition. It does not permit `(Litex.In.rep a haR : ℂ)`: the result type
of `In.rep` is fixed by the set in its membership proof, so `haR` selects
`Litex.R.Carrier = ℝ`, not `Litex.C.Carrier = ℂ`. It also does not permit
omitting `In.rep` or substituting an unrelated `C`-membership proof.

When the target carrier is not forced unambiguously by the operator, another
operand, or an expected type, Lean source construction must retain an explicit coercion or
fail closed rather than rely on unstable elaboration.

## Native Mathlib Corollaries

Status: confirmed target interface; not yet fully implemented.

A supported user theorem should have two Lean views. Its canonical theorem is
the exact FactId/proof-provenance target and retains implicit host carriers,
`Litex.In`, `Litex.Same`, and the verifier-selected representatives. When
reviewed elimination theorems can remove those wrappers without changing the
statement, compiler may additionally expose an ordinary Mathlib-facing
corollary. For example:

```litex
thm litex_real_add_comm:
    ? forall a, b R:
        a + b = b + a
```

has the intended Lean-facing corollary type:

```text
theorem litex_real_add_comm (a b : ℝ) : a + b = b + a
```

The corollary must be derived from the canonical theorem through allowlisted,
fully proved wrapper bridges. It must not ask Lean to rediscover the proof,
lose the source FactId route, add an axiom or proof hole, or force a native
statement when elimination is not lossless. If no reviewed elimination route
exists, compiler emits only the canonical theorem.

## Direct Recursive Result Architecture

## Design Goal

The compiler does not ask Lean to rediscover why a Litex statement succeeded.
Litex execution returns one recursive, typed result that records the successful
route from its leaves to its statement root. The compiler consumes that result
and deterministically replays the selected route as Lean declarations and
proof terms.

## Boundary and Completion of This Migration

This document uses two version labels only to describe the migration:

- compiler v1 meant the removed pipeline that first copied execution into a
  separate mirrored statement/proof tree and then rendered that tree as Lean;
- compiler v2 means the current `StmtResultToLeanCompiler`, which reads the
  completed recursive `StmtResult` directly and maintains a target-language
  environment stack while it constructs Lean source.

The completed scope of this round is exact:

- every Litex source accepted by compiler v1's reviewed test and persistent
  example surface is compiled through v2;
- the old statement-to-Lean module, mirrored statement/proof types, builder,
  label-to-rule fallback, public exports, and tests that asserted old type
  names have been physically removed;
- compilation happens after the execution `Runtime` is dropped, so the
  compiler cannot recover missing evidence from the live kernel environment;
- successful CLI output is JSON v2 produced directly from `StmtResult`, and
  result graphs are read-only presentations of the same returned structure;
- unsupported Result shapes fail closed. The migration does not claim to add
  Lean support for every Litex program that the kernel can execute.

The following work is deliberately outside this round:

- changing Litex execution semantics, statement atomicity, `FactId`
  allocation, or `Runtime`/`Environment` ownership;
- inventing a successful Result for `RuntimeError`, or compiling `Unknown`;
- broadening compiler coverage beyond the old reviewed compiler surface;
- removing unrelated kernel compatibility methods merely because they are
  currently private and unused.

That boundary keeps one invariant testable: deleting compiler v1 must not
change whether an existing Litex program executes. It may change compiler
errors for unsupported targets, JSON shape, graph shape, and generated Lean
spelling, but the reviewed v1-supported sources must still reach Lean and pass
the Lean kernel.

The canonical execution boundary is:

```rust
Result<StmtResult, RuntimeError>
```

These cases have deliberately different meanings:

- `Ok(StmtResult::Success(...))` is a completed statement result that may be
  rendered, graphed, or offered to a backend.
- `Ok(StmtResult::Unknown(...))` records that execution completed without a
  proof. It is useful for diagnostics but cannot be compiled to Lean.
- `Err(RuntimeError)` is an execution failure. There is no successful result
  to lower.

`Success` is used instead of `Verified` because successful execution also
includes explicit source trust, axioms, commands, and definitions. `Result` is
used instead of `Ir` because this is the direct output of kernel execution,
not a compiler-only intermediate representation.

The core types live in
[`stmt_result.rs`](../result/stmt_result.rs) and
[`success_stmt_result.rs`](../result/success_stmt_result.rs):

```rust
pub enum StmtResult {
    Success(SuccessStmtResult),
    Unknown(UnknownStmtResult),
}

pub enum SuccessStmtResult {
    Fact(Box<SuccessFactStmtResult>),
    UnsafeStmt(SuccessUnsafeStmtResult),
    DefObjStmt(SuccessDefObjStmtResult),
    DefPredicateStmt(SuccessDefPredicateStmtResult),
    DefInterfaceStmt(SuccessDefInterfaceStmtResult),
    DefAlgoStmt(Box<SuccessDefAlgoStmtResult>),
    DefThmStmt(Box<SuccessDefThmStmtResult>),
    AxiomStmt(Box<SuccessAxiomStmtResult>),
    DefStrategyStmt(Box<SuccessDefStrategyStmtResult>),
    By(SuccessByStmtResult),
    Witness(SuccessWitnessStmtResult),
    ProofBlock(SuccessProofBlockStmtResult),
    Command(SuccessCommandStmtResult),
}
```

The outer variants mirror the semantic statement families in `Stmt`. Every
payload with meaningful fields is a separately named structure. Large enum
payloads and recursive single children use `Box`; shared proof and
well-definedness nodes use `Rc`; ordered sibling results use `Vec`. This keeps
`StmtResult` small while preserving the complete recursive structure.

## End-to-End Flow

```text
Litex source
  -> parse Stmt
  -> exec_stmt
       -> statement-specific exec_* function
            -> well-definedness verify_* result
            -> proof verify_* result
            -> store/infer result
       -> finish statement while Runtime is alive
            -> attach exact FactIds
            -> attach execution trace
  -> one completed StmtResult
       |-> JSON v2 / result graph
       `-> StmtResultToLeanCompiler
            -> match the SuccessStmtResult family
            -> enter named recursive child Result fields
            -> push/pop compiler environments at lexical boundaries
            -> construct Lean declarations and proof terms directly
            -> Lean kernel
```

The completed `StmtResult` is the single semantic source for consumers. JSON,
graphs, summaries, and the StmtResult-to-Lean compiler traverse its fields; they do
not reconstruct successful execution by diffing a `Runtime` or by parsing
diagnostic text.

[`compile_litex_source_to_lean_source.rs`](compile_litex_source_to_lean_source.rs) intentionally executes the whole source, keeps the
ordered `Vec<StmtResult>`, drops the execution `Runtime`, and only then creates
`StmtResultToLeanCompiler`. Consequently the compiler cannot read facts,
definitions, WD caches, or names back out of the execution environment. If a
piece of evidence is absent from Result, compilation fails closed.

The public entry point has the same explicit input/output name:
`compile_litex_source_to_lean_source`. File and Markdown entry points are
`compile_litex_file_to_lean_file` and
`compile_litex_markdown_code_blocks_to_lean_file`. There is no ambiguous
`compile_source`, `emitter`, or `ledger` layer in the public API.

## Worked Data-Structure Trace: a `claim` with child statements

The smallest useful tracer is the first claim in
[`lean/examples/8_ProofScopes.lit`](../../lean/examples/8_ProofScopes.lit):

```litex
claim:
    ? 2 = 2
    2 = 2
```

For a programming-language implementation reader, the useful model is a pair
of stateful big-step interpreters:

```text
Litex execution:  <RuntimeEnv, Stmt>      ⇓ <RuntimeEnv', StmtResult>
Lean compilation: <CompilerEnv, StmtResult> ⇓ <CompilerEnv', LeanDecl*>
```

`StmtResult` is the proof-relevant handoff between the two. It is not merely a
success flag, a copy of the AST, a diagnostic trace, or a snapshot diff of the
runtime environment. Its recursive algebraic-data-type shape records the
successful control-flow branch, the verifier-selected evidence, ordered child
executions, exact identities, and which effects outlive a lexical scope. The
second interpreter consumes that value after the first interpreter and its
`Runtime` have been dropped.

This source contains one outer `ClaimStmt` and one user-written child
`FactStmt`. Execution also creates a second, synthetic child result for the
final conclusion check. That check is not another source statement: it is the
executor asking, after all proof steps have run, whether the claim target is
now known in the claim-local environment.

### 1. Execution constructs the recursive Result

For an ordinary, non-`forall` claim,
[`exec_goal_proof_block.rs`](../execute/exec_goal_proof_block.rs) performs these
operations in order:

1. Check that the target fact is well-defined.
2. Enter `run_in_local_env`.
3. Execute every source proof statement with `exec_stmt`, retaining one
   `StmtResult` per statement in `proof_steps`.
4. Verify the target once more and retain that synthetic `StmtResult` as
   `conclusion_check`.
5. While the local execution environment still exists, freeze all temporary
   `FactId`s into the recursive results.
6. Leave the local environment.
7. For a `claim` (but not an `example`), store the proved target in the parent
   environment and put that surviving store/inference effect in
   `SuccessClaimStmtResult.common.infers`.

Here is Rust-shaped pseudocode for the producer side. Bracketed comments name
the exact Result field written by each operation; error wrapping and trusted
file branches are omitted, but the ordering and ownership boundaries match the
current implementation in [`exec_stmt.rs`](../execute/exec_stmt.rs),
[`exec_claim_stmt.rs`](../execute/exec_claim_stmt.rs),
[`exec_goal_proof_block.rs`](../execute/exec_goal_proof_block.rs), and
[`exec_fact_stmt.rs`](../execute/exec_fact_stmt.rs).

```rust
fn exec_stmt(runtime, stmt) -> StmtResult {
    // Dispatches ClaimStmt to exec_claim_stmt and a child FactStmt to exec_fact.
    let mut result = exec_stmt_verified(runtime, stmt)?;

    // Recurses through every named child Result. It fills only missing IDs,
    // so an ID frozen before a local environment was popped is never retargeted.
    attach_known_fact_ids_to_stmt_result(runtime, &mut result)?;
    // [writes nested store.fact_id, citation.source_fact_id, infer FactIds]

    result = result.with_execution_trace(trace_for_this_statement());
    // [writes claim.common.execution_trace, or child_fact.execution_trace]
    result
}

fn exec_claim_stmt(runtime, stmt: ClaimStmt) -> StmtResult {
    let result = exec_checked_goal_block(
        runtime,
        stmt.clone().into(),
        &stmt.fact,
        &stmt.proof,
    )?;
    // [exec_checked_goal_block constructs statement + verification]

    let outer_infers = exec_claim_stmt_affect_environment(runtime, &stmt)?;
    // [produces the store of the proved target in the parent RuntimeEnv]

    result.with_infers(outer_infers)
    // [merges outer_infers into claim.common.infers]
}
```

The ordinary, non-`forall` branch of `exec_checked_goal_block` is the important
lexical-scope transition:

```rust
fn exec_checked_goal_block(runtime, source_stmt, target, source_proof)
    -> StmtResult
{
    let wd = verify_fact_well_defined_result(runtime, target)?;
    // [becomes verification.well_definedness]

    run_in_local_env(runtime, |local| {
        let mut proof_steps = Vec::new();
        for child_stmt in source_proof {
            proof_steps.push(exec_stmt(local, child_stmt)?);
            // [each complete child StmtResult becomes verification.proof_steps[i]]
        }

        proof_steps.push(verify_fact_return_err_if_not_true(local, target)?);
        // [becomes verification.conclusion_check]
        // This is a proof-only fact Result, not another source_proof element.

        for child in &mut proof_steps {
            attach_known_fact_ids_to_stmt_result(local, child)?;
            // [freezes local FactIds while local RuntimeEnv is still alive]
        }
        let conclusion_check = proof_steps.pop()?;

        let proof_scope = SuccessVerifyLocalProofScopeResult::new(
            SuccessInferResult::new(),
            Vec::new(),
        );
        // [becomes verification.proof_scope; empty for this atomic branch]

        let verification = SuccessVerifyClaimFactResult {
            fact: target.clone(),                 // [verification.fact]
            well_definedness: wd,                 // [verification.well_definedness]
            proof_scope,                          // [verification.proof_scope]
            proof_steps,                          // [verification.proof_steps]
            conclusion_check: Box::new(conclusion_check),
                                                    // [verification.conclusion_check]
        };

        SuccessClaimStmtResult {
            statement: source_stmt.into_claim(),  // [claim.statement]
            common: SuccessStmtCommonResult::new(empty_infers()),
                                                    // [claim.common, initially empty]
            verification: Some(Fact(Box::new(verification))),
                                                    // [claim.verification]
        }
    })
    // run_in_local_env pops the local RuntimeEnv before returning.
}
```

The child line `2 = 2` itself goes through the ordinary fact pipeline. This is
why a claim does not need a second, claim-specific representation of factual
proof evidence:

```rust
fn exec_fact(runtime, fact) -> StmtResult {
    let wd = verify_fact_well_defined_result(runtime, fact)?;
    // [child.well_definedness]

    let result = verify_fact_return_err_if_not_true(runtime, fact)?;
    // [constructs child.verification: Rc<SuccessVerifyFactResult>]
    // For 2 = 2, its proof is BuiltinRule(ObjectReflexivity(...)).

    let infers = store_without_well_defined_verification_and_infer(runtime, fact)?;
    // [child.store.infers; the actual local store/inference effects]

    result
        .with_fact_well_definedness(wd)
        .with_infers(infers)
    // finish_statement_execution later writes child.store.fact_id and
    // child.execution_trace.
}
```

The producer-to-field correspondence is therefore:

| Producer operation | Field in the outer claim Result | Meaning |
| --- | --- | --- |
| Claim AST cloning in `exec_checked_goal_block` | `statement` | What the user wrote: target and source proof statements. |
| `verify_fact_well_defined_result(target)` | `verification.well_definedness` | Evidence that the target can be formed before entering its proof scope. |
| `SuccessVerifyLocalProofScopeResult::new(...)` | `verification.proof_scope` | Assumptions intentionally installed at entry to the local proof environment. Empty in this tracer. |
| `exec_stmt(child_stmt)` | `verification.proof_steps[i]` | One complete, recursively typed execution result per user-written child, in source order. |
| Final `verify_fact_return_err_if_not_true(target)` | `verification.conclusion_check` | Synthetic proof-only Result showing that the target is known after all source proof steps. |
| Local `attach_known_fact_ids_to_stmt_result` | Fields inside `proof_steps` and `conclusion_check` | Freezes exact local store and citation identities before the Runtime scope disappears. |
| `exec_claim_stmt_affect_environment` followed by `with_infers` | `common.infers` | Effects exported by the claim to its parent environment. |
| Outer `finish_statement_execution` | `common.execution_trace` | Execution/trust provenance for this outer statement. |

Notice what does **not** happen: `run_in_local_env` does not return a generic
`local_scope: Box<StmtResult>`. It runs one precise semantic phase whose
outputs are already named `proof_scope`, `proof_steps`, and
`conclusion_check`. The Result follows the execution vocabulary instead of
wrapping the whole phase in an unrelated extra statement node.

The relevant named structures are defined in
[`success_stmt_result.rs`](../result/success_stmt_result.rs) and
[`runtime_success.rs`](../result/runtime_success.rs):

```rust
pub struct SuccessClaimStmtResult {
    pub statement: ClaimStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyClaimResult>,
}

pub struct SuccessStmtCommonResult {
    pub infers: SuccessInferResult,
    pub execution_trace: Option<StatementExecutionTrace>,
}

pub struct SuccessVerifyClaimFactResult {
    pub fact: Fact,
    pub well_definedness: SuccessVerifyFactWellDefinedResult,
    pub proof_scope: SuccessVerifyLocalProofScopeResult,
    pub proof_steps: Vec<StmtResult>,
    pub conclusion_check: Box<StmtResult>,
}
```

For the tracer above, the completed result has the following shape. The names
`f_local` and `f_claim` stand for two distinct allocated `FactId`s; their
numeric values are deliberately not part of this contract.

```text
StmtResult::Success
└─ SuccessStmtResult::ProofBlock
   └─ SuccessProofBlockStmtResult::ClaimStmt
      └─ SuccessClaimStmtResult
         ├─ statement: ClaimStmt
         │  ├─ target: 2 = 2
         │  └─ proof: [FactStmt(2 = 2)]
         ├─ common
         │  ├─ infers
         │  │  └─ parent store: (2 = 2, FactId = f_claim)
         │  └─ execution_trace: ...
         └─ verification: Some(Fact(...))
            └─ SuccessVerifyClaimFactResult
               ├─ fact: 2 = 2
               ├─ well_definedness: ...
               ├─ proof_scope
               │  ├─ assumption_infers: empty
               │  └─ assumption_components: empty
               ├─ proof_steps
               │  └─ StmtResult::Success(Fact)
               │     └─ SuccessFactStmtResult
               │        ├─ verification
               │        │  └─ proof: BuiltinRule(ObjectReflexivity(2 = 2))
               │        ├─ well_definedness: ...
               │        ├─ store
               │        │  ├─ fact: 2 = 2
               │        │  ├─ fact_id: Some(f_local)
               │        │  └─ infers: one local store output
               │        └─ execution_trace: verified
               └─ conclusion_check
                  └─ StmtResult::Success(Fact)
                     └─ SuccessFactStmtResult
                        ├─ verification
                        │  └─ proof: FactCitation(source_fact_id = Some(f_local))
                        ├─ well_definedness: ...
                        └─ store
                           ├─ fact: 2 = 2
                           ├─ fact_id: Some(f_local)
                           └─ infers: empty
```

The conclusion check retains `store.fact_id` because it is still a uniform
factual Result, but it publishes no new effect. Its decisive proof edge is
`verification.proof.FactCitation.source_fact_id = f_local`; that is what the
compiler resolves to the previously emitted local `have`.

Three boundaries in this tree are intentional:

- `statement` is the parsed source AST. It tells consumers what the user
  wrote, but not why execution succeeded.
- `verification` records the claim-local execution flow. Its `proof_steps`
  are exactly the user-written child statements, in source order;
  `conclusion_check` is the executor-created final check.
- `common` records effects of the outer claim statement that survive in the
  parent environment, plus its execution trace. Recursive child results do
  not belong in `common`.

`Box<StmtResult>` on `conclusion_check` is only the Rust indirection needed for
a single recursive child. `Vec<StmtResult>` expresses ordered sibling
children. Neither means that a generic, unrelated statement was added to the
claim: both fields name precise steps of `exec_checked_goal_block`.

### 2. The compiler executes that Result tree

The compiler does not re-run the Litex claim and does not consult the old
`Runtime`. It matches `SuccessClaimStmtResult`, then consumes the fields above
in their execution order:

| Result field | Compiler action | Scope/lifetime |
| --- | --- | --- |
| `statement.fact` and `verification.fact` | Validate that the retained verification belongs to this source target; render its Lean proposition. | Claim declaration |
| `verification.well_definedness` | Validate the evidence required to form the target proposition. | Claim declaration |
| `verification.proof_scope` | Validate that the current ordinary-fact route retained no local assumptions. A nonempty value is rejected rather than silently installed. | Claim-local frame |
| `verification.proof_steps` | Recursively compile each child `StmtResult` into local Lean proof steps. | Claim-local frame |
| `verification.conclusion_check` | Construct the final proof term from its recorded evidence and exact `FactId` citations. | Claim-local frame |
| `common.infers` | Validate the outer store and bind the parent `FactId` to the emitted theorem name. | Parent frame |
| `common.execution_trace` | Not consumed by the Lean compiler today. It remains available to JSON, graph, and audit consumers and is never proof search input. | Result metadata |

Rust-shaped pseudocode for that consumer path makes the producer/consumer
duality explicit. It follows
[`stmt_result_to_lean_compiler.rs`](stmt_result_to_lean_compiler.rs):

```rust
fn compile_all(results: &[StmtResult]) -> LeanSource {
    // The Litex Runtime has already been dropped here.
    let mut compiler = StmtResultToLeanCompiler::new();
    for result in results {
        compile_stmt_result(&mut compiler, result)?;
    }
    compiler.finish_lean_source()
}

fn compile_stmt_result(compiler, result) {
    match result {
        Unknown(_) => error("unknown Result cannot be compiled"),
        Success(ProofBlock(ClaimStmt(claim))) => compile_claim(compiler, claim),
        Success(other_family) => compile_that_result_family(compiler, other_family),
    }
}

fn compile_claim(compiler, claim: &SuccessClaimStmtResult) {
    let Fact(verification) = claim.verification.as_ref()
        .or_unsupported("ordinary claim needs retained Fact verification")?;

    let mut body = compile_ordinary_fact_goal_proof_body(
        compiler,
        &claim.statement.fact,
        claim.statement.proof.len(),
        verification,
    )?;

    // Consume claim.common.infers only after the local body has compiled.
    let f_claim = validate_exactly_one_outer_store(
        &claim.common.infers,
        &verification.fact,
    )?;

    body.local_proof_lines.push("exact " + body.conclusion_proof);
    let theorem_name = fresh_fact_name();
    emit_theorem(theorem_name, body.proposition, body.local_proof_lines);

    compiler.parent_env.fact_names[f_claim] = theorem_name;
    compiler.parent_env.fact_propositions[f_claim] = verification.fact;
}

fn compile_ordinary_fact_goal_proof_body(compiler, source_fact, n, verification) {
    require(verification.fact == source_fact);
    require(verification.proof_steps.len() == n);
    require(verification.proof_scope is empty); // current ordinary-fact contract
    validate(verification.well_definedness, source_fact)?;

    compiler.env.push_inherited_environment();
    let result = try {
        let lines = verification.proof_steps.enumerate().flat_map(|i, child| {
            compile_stmt_result_as_local_proof_steps(compiler, child, i + 1)
        })?;

        let conclusion = verification.conclusion_check.factual_success()?;
        require(conclusion.fact() == source_fact);
        require(conclusion.store.infers is empty);

        let final_proof = construct_lean_proof_from_direct_fact_result(
            compiler,
            conclusion,
        )?;
        let proposition = render_fact(source_fact, compiler.env)?;
        (lines, proposition, final_proof)
    };
    compiler.env.pop_local_environment();
    result
}
```

For the nested `FactStmt`, local compilation is another typed dispatch rather
than a recursive call to the top-level declaration emitter:

```rust
fn compile_fact_stmt_result_as_local_proof_step(
    compiler,
    child: &SuccessFactStmtResult,
    step_index,
) {
    require(child.store.fact == child.verification.fact());
    let f_local = child.store.fact_id
        .or_error("local fact needs a frozen FactId")?;
    validate_local_store_shape(&child.store.infers, f_local)?;

    let proof = construct_lean_proof_from_direct_fact_result(compiler, child)?;
    // Reads child.verification.proof():
    //   ObjectReflexivity     -> Litex.Same.refl ...
    //   Fact citation(f_local) -> resolve exact f_local in compiler.env

    // The selected proof adapter validates/uses child.well_definedness where
    // its object rendering requires it; the proposition is rendered in the
    // same active compiler environment.
    let proposition = render_fact(child.verification.fact(), compiler.env)?;
    let name = "__step" + step_index;
    compiler.env.fact_names[f_local] = name;
    compiler.env.fact_propositions[f_local] = child.verification.fact();
    emit_local_have(name, proposition, proof)
}
```

This compiler-side table states exactly which claim field is observed and
whether it contributes validation, proof construction, scope, or output:

| Result field | Read by | Concrete behavior |
| --- | --- | --- |
| `statement.fact` | `compile_claim_stmt_result_to_lean_source` and `compile_ordinary_fact_goal_proof_body` | Source-side target used for coherence checks and Lean proposition rendering. |
| `statement.proof.len()` | `compile_ordinary_fact_goal_proof_body` | Checks that execution neither lost nor invented a source proof step. |
| `verification` | `compile_claim_stmt_result_to_lean_source` | Must currently be `Some(SuccessVerifyClaimResult::Fact(...))`; another shape is unsupported, not guessed. |
| `verification.fact` | Claim/body compiler | Must equal `statement.fact`; also checked against the fact exported by `common.infers`. |
| `verification.well_definedness` | Body compiler and object renderer | Validates the target's retained WD tree before rendering proof terms that depend on it. |
| `verification.proof_scope` | Body compiler | Must be empty for the current ordinary atomic claim route; nonempty unexpected assumptions are rejected. |
| `verification.proof_steps[i]` | `compile_stmt_result_as_local_proof_steps` | Dispatches by the child's actual `SuccessStmtResult` variant and emits ordered local declarations. |
| Child fact `verification.proof()` | `construct_lean_proof_from_direct_fact_result` | Selects the exact Lean proof adapter recorded by Litex verification; no tactic search chooses a replacement route. |
| Child fact `well_definedness` | Local fact compiler/object renderer | Validates and renders objects in the proposition/proof. |
| Child fact `store.fact_id` | Local fact compiler | Creates the exact `FactId -> __stepN` binding used by later citations. |
| Child fact `store.infers` | Local fact compiler | Validates the local publication and compiles any supported typed inference children. |
| `verification.conclusion_check` | Body compiler | Must be a factual, effect-free check of the same target; its retained proof becomes the final `exact ...`. |
| Conclusion citation `source_fact_id` | Citation proof constructor | Resolves that exact ID in the active compiler frame; proposition matching or Lean `assumption` is not used as a substitute. |
| `common.infers` | Claim compiler | Must contain exactly the supported outer store; its persistent `FactId` is bound to the emitted theorem in the parent frame. |
| `common.execution_trace` | No Lean compiler method currently | Intentionally has no effect on generated proof terms. |

For this tracer, the compiler scope transition is:

```text
parent compiler frame
  push claim-local frame
    compile proof step
      f_local -> __step1
    compile conclusion check
      citation of f_local -> exact __step1
    finish the Lean proof body
  pop claim-local frame              # f_local is no longer visible
  emit theorem __fact3
  bind f_claim -> __fact3 in parent  # the proved claim remains visible
```

The corresponding maintained Lean output in
[`lean/examples/8_ProofScopes.lean`](../../lean/examples/8_ProofScopes.lean) is:

```lean
theorem __fact3 : Litex.Same (2 : ℂ) (2 : ℂ) := by
  have __step1 : Litex.Same (2 : ℂ) (2 : ℂ) := by
    exact Litex.Same.refl (2 : ℂ)
  exact __step1
```

This is direct recursive Result-to-Lean compilation. Helpers may temporarily
hold rendered Lean source fragments, but there is no second statement/proof IR
that mirrors `StmtResult` between these structures and the Lean source.

### Invariants and the nearest unsupported branch

The design is easiest to understand as an executable certificate with six
cross-checked invariants:

1. **Shape:** a source `ClaimStmt` must arrive through the matching successful
   enum path; an `Unknown` Result cannot be compiled.
2. **Arity and order:** `proof_steps.len()` must equal the AST proof length,
   and children are consumed in their retained order.
3. **Target coherence:** `statement.fact`, `verification.fact`, the
   `conclusion_check` target, and the outer exported fact must agree.
4. **Identity:** citations resolve an exact frozen `FactId`; equal rendered
   propositions do not make two stores interchangeable.
5. **Lifetime:** `f_local` is visible only while the claim compiler frame is
   pushed; `f_claim` is installed only after the theorem has been emitted into
   the parent frame.
6. **Evidence ownership:** the verifier selects the proof route and stores it
   under the factual child's `verification.proof`; the compiler validates and
   replays that route instead of rediscovering it.

The nearest structural branch is a `forall` claim. Its Result uses
`SuccessVerifyClaimResult::Forall`, a possibly nonempty `proof_scope`, and
`conclusion_checks: Vec<StmtResult>` rather than one `conclusion_check`.
Those fields already model the executor flow, but the current
`compile_claim_stmt_result_to_lean_source` direct path accepts only the
ordinary `Fact` variant and fails closed for the `Forall` variant. This section
therefore documents a real implemented vertical slice, not a claim that every
possible claim Result is already compilable.

## `StmtResultToLeanCompiler` and Its Environment Stack

`Runtime` is the executor whose structured source is Litex syntax. It owns
Litex execution state such as environments, active strategies, name scopes,
and memo tables. `StmtResultToLeanCompiler` is a second executor whose
structured source is the already completed recursive Result. Its state is
only target-generation state:

```rust
pub struct StmtResultToLeanCompiler {
    source_label: String,
    environment_stack: StmtResultToLeanCompilerEnvironmentStack,
    declarations: Vec<String>,
    next_fact_name_index: usize,
    next_local_inference_name_index: usize,
    next_sketch_namespace_index: usize,
}
```

Each compiler environment records names that already exist in the current
Lean scope: `SymbolId -> Lean name`, `FactId -> theorem name`, predicate and
function bindings, and the few representation bridges needed by the Lean
ABI. It never stores proof truth; proof truth remains in Result.
The stack and its frame bindings live in the explicitly named
[`stmt_result_to_lean_compiler_environment_stack.rs`](stmt_result_to_lean_compiler_environment_stack.rs),
separate from proof-construction functions.

The two recursive mechanisms have different jobs:

```text
SuccessStmtResult fields        StmtResultToLeanCompilerEnvironmentStack
------------------------        ----------------------------------------
say which child was executed    says which generated Lean names are visible
own proof/WD/rule evidence      maps exact SymbolId and FactId identities
define lexical body nesting     pushes on body entry and pops on body exit
remain after Runtime is dropped contains no independent truth or proof search
```

The compiler does not push merely because one Rust helper calls another.
It pushes exactly when the Result owns a target-language lexical body. A
dispatcher is `PassThrough`; a proof rule usually constructs a term in the
current frame; `forall`, function, existential, case, and isolated proof-block
bodies are `Combine` layers whose named child field creates a frame. Thus the
Rust call graph may be reorganized without changing Lean scope semantics.

The recursive compilation algorithm is therefore deliberately small:

```text
compile(result, current_environment)
  -> match the concrete SuccessStmtResult
  -> validate this layer against its named child Results
  -> if this layer owns a Lean lexical body:
       push an environment inherited from the current environment
       bind the body's parameters, assumptions, and local FactIds
       recursively compile the body's child Results in source order
       construct the enclosing Lean term/declaration while the frame is active
       pop the local environment
  -> otherwise recursively compile or cite children in the current environment
  -> publish only this layer's surviving SymbolId/FactId bindings
```

This makes the compiler an interpreter for `StmtResult`, parallel to—but
independent from—the kernel interpreter for `Stmt`:

```text
Runtime                                        StmtResultToLeanCompiler
-------                                        -------------------------
input: Stmt                                    input: completed StmtResult
state: Environment stack                       state: compiler Environment stack
frame knows Litex names/facts/strategies        frame knows Lean names for SymbolId/FactId
child Stmt may open a local Litex environment   child Result may open a local Lean scope
returns Success/Unknown/Error                   returns Lean source or a compiler error
```

The compiler stack is not an analogy used only in documentation. It is the
mechanism by which recursive Result ownership becomes Lean nesting:

```rust
pub struct StmtResultToLeanCompiler {
    environment_stack: StmtResultToLeanCompilerEnvironmentStack,
    declarations: Vec<String>,
    // deterministic target-name counters
}

struct StmtResultToLeanCompilerEnvironmentStack {
    environments: Vec<StmtResultToLeanCompilerEnvironment>,
}

struct StmtResultToLeanCompilerEnvironment {
    symbol_names: HashMap<SymbolId, String>,
    fact_names: HashMap<FactId, String>,
    fact_propositions: HashMap<FactId, Fact>,
    // target representations for visible functions and predicates
}
```

For a binder-owning Result, the operational order is exact:

```text
push inherited compiler environment
  install parameter SymbolIds
  install assumption FactIds
  compile typed inference child Results and install their FactIds
  recursively compile proof-step/conclusion child Results
  construct the enclosing Lean body before local names disappear
pop compiler environment
publish only the enclosing theorem/definition in the parent environment
```

### Compiler-private compiled results are not another IR

`StmtResult` is the only semantic input to the compiler. Nevertheless, a
compiler function sometimes has to return several target-language pieces to
its parent. Those pieces should also be named and structured until the final
Lean rendering boundary. They must not be packed into one `String` and then
parsed by another compiler function.

Typed inference uses the following compiler-private result:

```rust
struct CompiledInferenceFactProofStep {
    fact_id: FactId,
    fact: Fact,
    local_lean_name: String,
    proposition: String,
    proof_expression: String,
}
```

This type is deliberately not named `IR`. It does not record new proof truth,
mirror an inference rule, or survive compilation. `fact_id` and `fact` are
copied from the canonical Result; `local_lean_name`, `proposition`, and
`proof_expression` are target-source construction outputs. One instance can
be rendered in three places without recovering fields from Lean text:

```text
local proof body       -> have <name> : <proposition> := <proof>
anonymous-function body -> let <name> : <proposition> := <proof>
top-level publication -> theorem <published name> : <proposition> := ...
```

While compiling the next recursive step, the current compiler environment
must also know how the preceding proof can be cited. That target-only choice
is explicit:

```rust
enum CompiledInferenceFactAvailabilityInLeanEnvironment {
    LocalProofName,
    InlineProofExpression,
}
```

Proof blocks, anonymous functions, and top-level theorem publication use a
local name because their enclosing syntax can render the returned step.
Function-body construction can have no surrounding tactic block, so it
installs the proof expression itself. The same choice is passed recursively;
therefore a future nested inference never accidentally cites a local name that
its enclosing Lean term did not declare.

For `1 $in N`, execution returns the stored membership fact and its recursive
inference children. The compiler first produces a step for
`1 >= 0`; the next recursive step proves `(-1) * 1 <= 0` and its
`proof_expression` cites the first step's `local_lean_name`. When publishing
the second top-level theorem, the compiler renders the preceding structured
step inside its proof closure. It never performs the former reverse operation
of splitting `"have ... : ... := ..."` to rediscover the temporary name,
FactId, proposition, or proof.

The extension rule is intentionally small:

1. a new inference rule is validated against its typed Result fields;
2. its compiler method constructs one `CompiledInferenceFactProofStep` for
   each newly available fact, in dependency order;
3. the surrounding Result scope chooses how to render those steps;
4. an unsupported rule returns a compiler error before publishing a step.

This does not require another enum variant for every compiler helper. A helper
still declares one composition behavior: construct a target fragment, wrap or
combine child fragments, pass a child through, or reject an unsupported Result
shape. More compiler-private structs should be introduced only when two or
more fields must stay associated across a function boundary. Plain `String`
remains appropriate for a final Lean identifier, proposition, proof
expression, declaration, or already ordered source line. It is not
appropriate for carrying a FactId, source fact, child identity, scope, or rule
selection implicitly.

For a `ForallProof`, the proof-owned frame identities are explicit rather
than inferred from a flat store summary:

```rust
pub struct SuccessForallProofResult {
    pub forall_fact: ForallFact,
    pub parameter_assumptions: Vec<SuccessForallAssumptionFactResult>,
    pub domain_assumptions: Vec<SuccessForallAssumptionFactResult>,
    pub assumption_infers: SuccessInferResult,
    pub proves: Vec<SuccessForallProvedFactResult>,
}

pub struct SuccessForallAssumptionFactResult {
    pub fact: Fact,
    pub fact_id: FactId,
}
```

This distinction matters when a written domain premise repeats a parameter
fact. Runtime correctly performs no second store, so `assumption_infers` has
fewer store outputs than the source has assumption occurrences. The matching
`domain_assumptions` entry reuses the parameter's exact `FactId`. Sibling WD
Results may have their own check identities; the compiler binds those as
evidence aliases but never mistakes them for the proof-scope assumption.

For a non-binder Result, compilation stays in the current frame. A successful
set alias illustrates why both maps are required: `have A set = R` installs
the source `SymbolId -> A` and also installs the exact store identities for
`$is_set(A)` and `A = R`. A later nested membership inference cites the
equality by `FactId`; knowing only the Lean spelling `A` is insufficient.

A conjunction illustrates the same rule one level deeper. Storing
`p and q` returns typed `ConjunctionImpliesComponent` children. The compiler
binds their exact FactIds to the target projections `h.1` and `h.2` in the
current frame. A conclusion that cites `q` resolves that FactId; the compiler
does not search the current propositions for text equal to `q`.

There is deliberately no full `StmtResultToLeanIr` between this traversal and
Lean source. Each compiler method may create a short-lived Lean source
fragment or proof expression and return it to its parent, but it does not copy
the statement/proof tree. The recursive Result is the tree; the environment
stack supplies lexical target names while that tree is traversed.

Every execution or verification function declares one composition mode; it
does not automatically require a Result enum variant:

```text
Leaf        construct evidence without successful children
Wrap        retain one named child and add this layer's evidence
Combine     retain multiple named or ordered children and add this layer's evidence
PassThrough return the exact child's result unchanged
Reuse       cite an earlier frozen proof node or FactId
```

### Concrete compiler-environment-stack example

Consider this source statement:

```litex
forall r R+:
    r $in R
    r $in C
    r > 0
```

Its `ForallProof` Result owns the parameter-membership store, the typed
`PositiveStandardSetMembershipImpliesPositive` inference application, and the
three ordered conclusion Results. The compiler handles that ownership as one
lexical layer:

```text
compile outer SuccessFactStmtResult
  push inherited compiler environment
    bind parameter SymbolId       -> r
    bind parameter FactId         -> __h6_1
    compile typed infer Result
      have __infer6_0 : Litex.Positive r :=
        Litex.Rules.positiveOfInRPos (__h6_1)
    bind inferred FactId          -> __infer6_0
    compile conclusion 1          -> Litex.In r Litex.R
    compile conclusion 2          -> Litex.In r Litex.C
    compile conclusion 3          -> cite inferred FactId
    finish the forall proposition and proof while these bindings are visible
  pop local compiler environment
  publish only the completed forall theorem in the parent environment
```

There is no `ScopedBinderIr` or `ScopedFactIr` to reconstruct. The recursive
Result fields already say which facts belong to the forall body; the compiler
environment stack only gives those exact `SymbolId` and `FactId` values Lean
names for the lifetime of that body. The generated pair is
[`21_PositiveRealCarrier.lit`](../../lean/examples/21_PositiveRealCarrier.lit)
and
[`21_PositiveRealCarrier.lean`](../../lean/examples/21_PositiveRealCarrier.lean).

The environment frame is intentionally narrower than a kernel `Environment`.
It may contain `SymbolId -> Lean name`, `FactId -> Lean proof name`, source
propositions used to validate those exact IDs, and target-representation
bindings for functions and predicates. It must not contain an alternative
proof tree, verifier labels interpreted as rules, a cache used to rediscover a
proof, or a reference to `Runtime`. Those belong in the recursive Result or
are not legitimate compiler inputs.

The current Rust implementation represents a child frame as an inherited
snapshot of all bindings visible at entry plus that child's local additions.
This makes lookup and the migration from the old compiler straightforward:
insertions affect only the top frame, and `pop_local_environment` discards the
whole local layer. A future implementation may store only per-frame deltas and
walk parent frames during lookup, but that is an internal space/time tradeoff;
it must not change the Result structure, lexical push/pop boundaries, exact
`FactId` resolution, or generated Lean.

For example, a successful fact statement is compiled as one statement layer:

```text
SuccessFactStmtResult
  well_definedness -> recursively compiled WD checks
  proof            -> recursively compiled selected verification route
  store            -> publish the source FactId
    infers         -> recursively compile typed inference Results and publish their FactIds
```

The compiler stack answers whether each cited identifier is visible at the
point where that layer is translated. It does not answer why any of those
facts are true.

An `eval` statement follows the same rule. Ordinary execution returns a named
`SuccessEvaluatedEvalStmtResult` containing the exact source object, evaluated
object, and an optional recursive numeric computation. A closed numeric
computation is compiler-ready: the compiler validates the tree, emits the
equality proof, and publishes the equality store's final `FactId` in the
current environment. The JSON `reported_store_facts` view is projected from
that canonical store after IDs are attached; it is not a second snapshot.
An evaluation performed by a runtime algorithm without typed computation
evidence remains explicit in Result and fails closed at the standalone compiler
boundary.

`clear` is the non-lexical counterpart. Its successful Result has no proof
child and no mathematical effect, but it explicitly replaces the current
compiler environment with an empty frame. Previously generated Lean text
cannot be deleted, so the compiler opens `__AfterClearNN` for subsequent
declarations; this permits a later Litex definition to reuse a source spelling
without colliding with the earlier Lean name. Successful `do_nothing` and
strategy activation/deactivation commands are true `PassThrough` layers: they
validate that no mathematical effects were published and emit no Lean
declaration. A Result stream containing only such commands still compiles to a
valid declaration-free Lean namespace.

The stack follows Result ownership. A top-level statement uses the root
environment. A `sketch` pushes an inherited child environment, recursively
compiles its `proof_steps`, emits those declarations inside a namespace, then
pops the child. A successful `try` recursively compiles its committed children
in the current environment. Forall, existential, case, and function bodies
use the same rule: the Result field that owns the body determines where the
compiler environment is pushed and popped. `run_in_local_env` in the kernel is
therefore not a compiler problem; its returned children are already nested in
the parent Result.

The local-layer helper restores the outer environment, declarations, and name
counters before propagating an error. Therefore a rejected inner Result cannot
leave half of a Lean scope in compiler state. The compiler does not publish
partial output when construction fails.

Predicate-property registration is a concrete example of a compiler binding
that belongs in this stack but is not a Litex fact. A successful
`by reflexive_prop` Result has this shape:

```text
SuccessByReflexivePropStmtResult
  verification: SuccessVerifyByPropRegistrationResult
    well_definedness
      recursive forall binder, premises, and conclusions
    assumption_infers
      parameter/domain stores with frozen local FactIds
    proof_steps
      ordered statement Results executed in that binder
    forall_check
      complete SuccessFactStmtResult for verify_forall_fact
        ForallProof
          assumption_infers
          proves
            one Result per checked conclusion
```

The field is called `forall_check`, not `conclusion_check`, because it owns the
whole recursive `verify_forall_fact` output. The compiler validates that its
nested assumptions and conclusions agree with the registration wrapper,
pushes an inherited environment, compiles those children, and pops it. It then
publishes a `RegisteredPredicatePropertyTheoremBinding` only in the current
outer compiler environment. Later typed builtin evidence cites the predicate
name and resolves this target-side binding; it does not search Runtime facts
or parse the verifier's diagnostic label.

The same Combine function compiles symmetric, transitive, and antisymmetric
registrations. Their `dom_facts` become ordered Lean hypotheses such as
`__domain1` and `__domain2` in the same frame. When assuming a concrete
predicate also infers one of its defining clauses, the assumption store owns
that inferred FactId; the compiler projects the exact clause from the named
domain hypothesis and installs the projection under that ID. No proposition
lookup crosses the frame boundary.

Later uses exercise three different composition modes. Registered reflexivity
is a leaf. Registered symmetry is a `Wrap` whose sole child is the reordered
predicate premise; the compiler may apply the registered permutation theorem
more than once when the permutation is not an involution. Registered
antisymmetry is a `Combine` with two ordered predicate-premise children.
Registered transitivity appears in the store/infer Result rather than the
verifier proof Result: storing a relation chain returns one typed closure
application for every object interval. Each application owns its predicate
name, start/end object indices, ordered adjacent premise facts with exact
FactIds, and its stored conclusion with an exact FactId.

The transitive-chain compiler first publishes the theorem for the whole source
chain. It then maps each adjacent premise FactId to the corresponding `.1` /
`.2...` projection of that theorem in the current compiler environment. For
each typed closure application it resolves the previously registered
transitivity theorem from the environment stack, folds that theorem over the
ordered premise projections, and publishes the conclusion under the Result's
FactId. A later statement can therefore cite the inferred fact by FactId in
the ordinary way. The compiler never asks Runtime whether the predicate was
transitive and never searches for two propositions that happen to have the
right text.

Ordinary concrete-predicate inference now follows the same rule instead of
remaining a flattened side effect. Execution returns one named application
for every parameter requirement and definition clause:

```rust
pub enum InferRule {
    DefinedPredicateParameterRequirementProjection(
        DefinedPredicateParameterRequirementProjectionInferRule,
    ),
    DefinedPredicateDefinitionClauseProjection(
        DefinedPredicateDefinitionClauseProjectionInferRule,
    ),
    // ...
}
```

Each application owns the predicate name, exact component index, one source
premise with its `FactId`, and one recursive `SuccessStoreFactResult`
conclusion. The conclusion may itself contain further typed inference Results.
The parent keeps only an ordered compatibility summary of store effects;
nested rule applications are reached through the conclusion field and are not
flattened into a second proof list.

This family also shows why the compiler needs an environment stack. At top
level, a conclusion such as `R = C` becomes a persistent Lean theorem and its
`FactId` is added to the current root frame. Inside a forall proof, the same
projection becomes a local proof expression derived from `__domain1`; its
`FactId` is added only to the inherited child frame and disappears at pop.
The semantic Result is identical in both cases. Only the target-language
publication policy differs with the active compiler environment. The complete
source/Lean pair is
[`47_DefinedPredicateInferenceCompilerEnvironment.lit`](../../lean/examples/47_DefinedPredicateInferenceCompilerEnvironment.lit).

For a source binder `x set`, the Result deliberately still contains the
checked `$is_set(x)` premise and its FactId. Lean already expresses that fact
by the type `x : Litex.Set`, so the compiler's explicit proposition/proof
bridge is `True` / `True.intro`. This preserves the child Result and its exact
identity without inventing a fictitious membership carrier.

A child layer returns every target fragment that still depends on its local
bindings before the environment is popped. For example, direct forall
compilation returns both its rendered Lean proposition and its proof
expression. The parent publishes that pair as a theorem; it does not
re-render the proposition after the parameter/domain FactIds have disappeared.
This is the compiler analogue of an `exec_*` or `verify_*` child returning its
completed Result for the caller to wrap.

Finite-sequence definitions show why this stack belongs to the compiler rather
than in another proof IR. A `SuccessHaveFiniteSeqStmtResult` has two checked
bound children at statement scope. Its verification child then owns one local
parameter store, one local domain-premise store, and one recursive return check:

```text
SuccessHaveFiniteSeqStmtResult
  verification
    bound_checks
      bound in N+
      bound = finite_sequence_length
    well_definedness
      surface_set
      anonymous_function
      function_set
    assumption_infers
      store index in N+       -> local FactId F_parameter
      store index <= bound    -> local FactId F_domain
    return_check
      body in return_set
  common.infers
    store named value in finite_seq(...) -> persistent FactId F_surface
    infer named value in fn(...)         -> persistent FactId F_function
    store named value = anonymous fn     -> persistent FactId F_definition
```

`compile_have_finite_sequence_stmt_result_to_lean_source` first consumes the
two outer checks, then pushes an inherited compiler environment. It binds the
index name, maps `F_parameter` to the Lean membership argument, maps `F_domain`
to the Lean domain argument, and recursively consumes `return_check`. It pops
that environment before registering the three persistent FactIds. Thus the
nesting is expressed once by Result fields and executed once by the compiler
stack; neither `run_in_local_env` nor a separate scoped-fact IR needs to be
reconstructed.

The matrix path applies exactly the same rule with larger named collections:
four `bound_checks` belong to statement verification; two parameter stores,
two domain stores, and `return_check` belong to one child environment. The
compiler does not invent nested row/column scope records. It enters the one
Result-owned function layer, installs all four local FactIds in source order,
compiles the body, and pops once. This is the intended scaling law: Result
field nesting determines scope depth, while ordered sibling vectors determine
work inside one scope.

For example, `have chosen R` is compiled by reading its nested Result directly:

```text
SuccessHaveObjInNonemptySetStmtResult
  verification
    SuccessVerifyObjectChoiceResult
      nonempty_check
        Fact: $is_nonempty_set(R)
          BuiltinRuleEvidence::StandardSetNonempty
            target_set: R
  common.infers
    store: chosen $in R, FactId F_chosen
```

The child evidence selects `Litex.Rules.realNonempty`. The parent layer creates
the Lean object with `Classical.choice`, then registers `F_chosen` in the current
compiler environment. Changing the builtin diagnostic label cannot change the
generated Lean source.

An equality-backed object definition is another direct `Combine`. For
`have y R = 1`, `SuccessHaveObjEqualStmtResult` owns the checked source value,
the nested `type_checks` fact Result, and the ordered store effects for
`y $in R` and `y = 1`. The compiler constructs `y`, then registers the two exact
FactIds in that order. It does not first copy the statement into a mirrored
compiler-only statement node. Checked set aliases use the
same parent Result to install their names in a child compiler environment, so
leaving a `sketch` removes those bindings automatically.

An ordinary-carrier `trust have` is an explicit trust-boundary `Combine`.
`SuccessTrustHaveStmtResult` owns the source-ordered parameter groups followed
by any attached facts, while `common.infers.store_fact_outputs` owns their
exact environment identities in the same order. The compiler emits each
trusted object as an explicit Lean axiom, proves its `Litex.In` wrapper from
the exact declared carrier, registers the retained membership `FactId`, and
then emits attached facts as explicit axioms. A trusted function carrier also
installs its callable contract under that same FactId, so a later application
uses the ordinary compiler environment lookup. This slice intentionally
fails closed for set/refined-set bindings and parameter stores with inferred
siblings; it never silently broadens an object trust boundary into a generic
universal carrier.

A reviewed named-function definition now follows the same rule all the way
through. For `have fn reciprocal(x R: x != 0) R = 1 / x`, the compiler
reads this ownership tree:

```text
SuccessHaveFnEqualStmtResult
  verification: SuccessVerifyFunctionDefinitionResult
    assumption_infers
      store x $in R, temporary FactId F_parameter
      store x != 0, temporary FactId F_domain
    return_check
      Fact: 1 / x $in R
        BuiltinRuleEvidence::RealArithmeticMembershipClosure(Div)
          subgoal
            Fact: 1 $in R and x $in R
  common.infers
    store reciprocal $in fn(...), persistent FactId F_membership
    store reciprocal = fn(...), persistent FactId F_definition
```

`compile_have_fn_equal_stmt_result_to_lean_source` pushes an inherited
compiler environment for `verification`, binds `x` to the generated Lean
argument name, binds `F_parameter` and `F_domain` to the corresponding local
hypotheses, and consumes the recursive `return_check`. It then pops that
environment before emitting and registering the two persistent outer facts.
Consequently the temporary binder facts cannot escape, while later function
applications cite `F_membership` and `F_definition` exactly. Unary functions,
domain-constrained functions, and multi-parameter telescopes use this direct
path. A native-real return renders its checked real body directly. A non-real
return such as `{z R: z = z}` consumes the recursive membership proof and
constructs `Litex.In.rep source_body return_proof` while the parameter frame is
active. Function reduction later needs only the stored definition `FactId` and
the source body under exact argument substitution; it does not retain a second
compatibility return-selection proof tree.

The compiler keeps `LeanTargetFunctionTypeRepresentation` and
`LeanTargetObjectRepresentation` because they describe target-representation
choices. It does not construct a duplicate statement-result node on this
path. The short-lived
`CompiledNamedFunctionDefinitionBody` contains only the Lean construction
output that the parent Result method needs to emit its declarations; it is not
a second semantic statement tree.

A local object definition inside a theorem demonstrates the same stack rule
without a mathematical binder. When a proof step is `let z = 2`, the compiler
inserts `SymbolId(z)` and the defining equality's exact `FactId` into the
current theorem frame and emits a local Lean `let` plus `have`. The following
`z = 2` Result resolves those bindings normally. Popping the theorem frame
removes both; no `run_in_local_env` marker or scoped-fact wrapper is required
in the Result.

Cross-statement reuse can make the child proof richer than a fresh isolated
run. In the complete named-function tracer, the later proof of `1 $in R` may
cite the earlier WD store `id(1) $in R` and retain the equality edge
`id(1) = 1`. Before compiling the enclosing equality, the compiler therefore
walks the atomic fact's recursive object-WD Result and installs its exact
intrinsic-result store FactIds. A later citation then reads its ordered
`EqualityTransportEvidence.steps`; each step must carry the exact equality
FactId and orientation, and is emitted through `Litex.In.congr`. No
proposition lookup or equality search is performed. This is a concrete reason
that WD stores and proof transforms must travel upward inside Result rather
than live only in a `Runtime` side table.

An indexed tuple makes the same ownership rule visible for an object-WD child
rather than a fact-proof child. `SuccessHaveTupleStmtResult.verification` is a
`SuccessVerifyTupleOrCartDefinitionResult`: it owns the recursive
`value_well_definedness` returned while the source index is locally bound, and
a named `dimension` result owning the positive and at-least-two fact Results.
The compiler validates both ambient dimension proofs, pushes an inherited
environment for the source index, validates and renders the coordinate value
from its recursive WD Result, then pops that environment. Only afterward does
it publish the exact ordered `IsTuple`, dimension, and coordinate-forall
FactIds. No mirrored tuple-statement compiler node is constructed on this path. The
persistent pair is
[`29_IndexedTupleCompilerEnvironment.lit`](../../lean/examples/29_IndexedTupleCompilerEnvironment.lit)
and its generated Lean file.

An indexed sequence extends the same rule from one local object check to a
whole local function-verification layer. `SuccessHaveSeqStmtResult` owns a
`SuccessVerifyIndexedFunctionDefinitionResult`. Its `well_definedness` field
is a `SuccessVerifyIndexedFunctionDefinitionWellDefinedResult` with three
named recursive children: `surface_set`, `anonymous_function`, and
`function_set`. Its `assumption_infers` field retains the local
`index $in N+` Store and exact `FactId`; `return_check` retains the proof that
the source body belongs to the result set.

`compile_have_sequence_stmt_result_to_lean_source` therefore performs this
composition directly:

```text
SuccessHaveSeqStmtResult
  -> validate surface_set / anonymous_function / function_set WD Results
  -> push inherited StmtResultToLeanCompilerEnvironment
       install index SymbolId -> __arg
       install local index-membership FactId -> __arg_in
       consume recursive return_check
       compile the real-valued function body
     pop local environment
  -> publish surface-membership FactId
  -> publish inferred function-membership FactId
  -> publish defining-equality FactId
```

The local index and its temporary FactIds cannot be observed after the pop.
The callable contract deliberately keeps the surface membership FactId chosen
by Runtime; the separate inferred function-membership FactId is also
published, but is not substituted for the verifier-selected identity. Lean's
`sequenceSet values` is definitionally `fnSet NPos values`, so both facts
refer to the same exact function carrier without a universal object box. The
persistent pair is
[`30_IndexedSequenceCompilerEnvironment.lit`](../../lean/examples/30_IndexedSequenceCompilerEnvironment.lit)
and its generated Lean file. Its following function application checks that
the parent compiler environment retained only the three intended outer facts.

A Template definition is another nested statement composition, not a new IR.
`SuccessDefTemplateStmtResult.template_parameter_groups` owns only the
Template header binders, while `body_statement_result` owns the parameters of
the declaration inside the Template body. For example, in
`template<S set>: have sequence set = fn(n N+) S`, `S` belongs to the outer
Template Result and `n` belongs to the nested function-set value. The box
around `body_statement_result` breaks the recursive Rust type size; it does
not mean that the local environment executed an unrelated generic statement.

The initial direct compiler slice accepts one or more `set` Template
parameters, no Template domains, and exactly one body of the form
`have <name> set = <value>`. Instantiating an exact application retains either
`SuccessTemplateInstantiationResult::Created`, with argument checks, the
preverified body Result, and public equality stores, or `Reused`, with the
same application identity. A sequence-family Template therefore compiles to
`Litex.fnSet Litex.NPos S`; it does not use Lean's zero-based sequence types
and performs no index shift. Template domains, non-set parameters, and other
body families fail closed until they receive their own Result-driven
compiler route. The persistent pair is
[`55_TemplateSequenceInstantiationResult.lit`](../../lean/examples/55_TemplateSequenceInstantiationResult.lit)
and its generated Lean file.

Concrete `by def` is also a direct `Combine`.
`SuccessVerifyByDefinitionResult` retains the selected `DefPropStmt`, ordered
argument-check Results, instantiated clause facts, and ordered clause-check
Results. `CompiledByDefinitionProofBody` keeps the target proof separate from
the component proofs. The target is emitted by unfolding the active predicate
and combining those exact children. The outer store effect then determines
which component facts became environment-visible: every new inferred FactId
must match a recursive child Result with the same retained FactId, while an
already-visible FactId is reused without a duplicate declaration. Builtin
definition families remain on the explicit compatibility route.

An ordinary `claim` or `example` now uses the environment stack for its proof
body directly. `SuccessVerifyClaimFactResult.proof_steps` are compiled in
source order into local Lean `have` declarations. Each local fact registers
its own frozen `FactId` only in the inherited child compiler environment, and
`conclusion_check` must cite that exact ID. The child environment is popped
before a claim publishes its distinct outer store FactId; an `example`
publishes no outer fact at all. The compiler rejects a Result that retargets a
local store to a later ambient fact merely because both propositions render
the same way.

A named theorem uses the same composition rule. Its recursive forall
well-definedness Result establishes the binder and conclusion shape; its
proof-scope parameter stores provide the exact local FactIds; its ordered
`proof_steps` run in an inherited compiler environment; and its
`conclusion_checks` Results construct the final Lean proof. Popping that child
environment removes parameter and proof-step facts before the theorem's
distinct outer FactId is registered under the source theorem name. The direct
route currently covers no-binder theorems, ordinary object binders over
reviewed standard-set carriers, heterogeneous object binders over a preceding
set binder, atomic conclusions, and the reviewed one-witness existential
conclusion. Dependent/refined binders, domain premises, the other non-atomic
conclusion families, and exported theorem projections remain on the explicit
compatibility path.

The matching direct `by thm` route closes the reference loop. Execution stores
the exact source theorem `FactId` in `SuccessVerifyByTheoremResult`; the
compiler resolves only that ID, combines the recursively retained argument
membership checks, applies the Lean theorem, and registers each direct
conclusion under its own store FactId. A theorem name or proposition string is
display information, never a substitute for the source identity.

A positive one-witness existential introduction is also a direct `Combine`.
`SuccessWitnessExistFactResult` owns its ordered local `proof_steps`, the
witness `parameter_checks`, the instantiated `body_checks`, and the outer
existential store. The compiler pushes an inherited environment for the local
steps, registers their exact FactIds, constructs the Lean witness tuple from
the two checked child proofs, then pops that environment before registering
the existential's outer FactId. The current direct slice deliberately retains
the existing one-witness, one-body-fact boundary; multiple witnesses,
`exist!`, and `not exist` still fail closed or use an explicitly identified
compatibility route.

The matching existential-elimination family shares one direct `Combine`.
Four statement adapters cover explicit `obtain y from exist ...`, an object
definition with a fact body such as `have y R: ...`,
`obtain y from $concrete_predicate(...)`, and `obtain y from thm ...`. Each
adapter validates only how its statement formed the common
`SuccessVerifyExistentialEliminationResult`; one shared compiler method then
reads the recursively retained source proof, introduces the selected object,
and publishes the two projection effects.

For a concrete predicate source, the nested fact Result contains
`BuiltinRuleEvidence::DefinitionProjection` and its exact predicate-proof
child. The compiler verifies the retained `DefPropStmt` against the active
predicate binding, unfolds that child proof, and selects the matching
existential clause. It does not ask `Runtime` to instantiate the definition
again. For all three adapters the source is resolved by exact `FactId`, the
source existential binder is validated in a temporary compiler environment,
and only the selected Lean object plus the witness-type/body projection
FactIds remain visible afterward. Alpha-renamed existential binders attached
to the same `FactId` are checked structurally rather than compared as display
strings. The projection proofs come from `Classical.choose_spec`; no
proposition-string fact lookup or live `Runtime` lookup is involved.

The theorem-backed adapter demonstrates proof construction versus
publication more explicitly. A named
`CompiledLitexTheoremInstantiationConclusionProofBody` is constructed from
the nested `SuccessByThmStmtResult`. A top-level `by thm` requires and
publishes each conclusion's retained FactId. Inside `obtain from thm`, the
temporary conclusion may intentionally have no publishable FactId after its
execution-local environment is popped; the parent consumes its exact proof
body and publishes only the witness projections. No compiler environment
binding escapes merely because the nested Result was compiled.

`by cases` and `by contra` use the same environment discipline directly.
`SuccessVerifyByCasesResult` combines its coverage child, ordered branches,
branch assumption FactIds, structural assumption-component FactIds, local
proof-step Results, and either conclusion or contradiction exits. Each branch
runs in a separate inherited compiler environment. `SuccessVerifyByContraResult`
installs its exact reverse-assumption FactId in another inherited environment,
compiles its ordered local steps, and combines the two complementary factual
children in `SuccessVerifyContradictionResult`. Neither direct route first
constructs mirrored case-branch or reverse-assumption nodes.

Proof construction and publication are separate operations. A
`CompiledFactProofBody` contains the proposition and its Lean proof but does
not invent a FactId. If the statement Result contains a matching store output,
the compiler publishes the proof under that exact FactId. If execution
returned no store output because the fact was already known, the compiler
requires the same fact to be visible in the current environment and emits no
duplicate top-level theorem. A branch conclusion may itself retain local
store/infer children; those children are validated as part of that recursive
fact check and disappear when the branch environment is popped.

Function applications additionally need the verifier-selected WD object-use
context while their Lean term is rendered. During this migration the compiler
projects only the relevant recursive WD Result into a temporary rendering
certificate. It does not construct a mirrored statement or fact-proof IR, and
the previous compiler WD context is restored immediately after rendering.
For an exact declared return carrier, the WD subtree owns
`FunctionApplicationReturnMembership` and its head-contract child. The outer
fact proof normally does not duplicate that rule: it cites the WD-produced
membership by its exact `FactId`. The compiler activates that statement's WD
tree, resolves the citation in the same environment layer, and renders
`Litex.In.own` for the retained application occurrence. A memo-shared builtin
with the same typed evidence uses the same constructor; neither path searches
for a function declaration by proposition text.

`FactTransformationEvidence` is consumed as the recursive `Wrap` that its
Result shape describes. The compiler first constructs the cited/source proof,
then walks `steps` in source-to-target order. Rational normalization validates
the complete atomic-fact shape before emitting Lean `convert`; equality
rewrite validates every retained equality `FactId`, orientation, and current
endpoint. The final intermediate fact must equal the enclosing target exactly.
There is no target-side search for a replacement equality and no flattening of
the ordered steps into a diagnostic label.

Checked named-function reduction is a different `Leaf`, not an implicit
transformation search. `CheckedFunctionDefinitionReductionEvidence` records
the defining equality's exact `FactId`, which side of the goal is the
application, the one-step reduced object, and the other side that it matched.
The compiler resolves that FactId through its current environment stack,
checks the retained orientation and alpha-equivalent result, then unfolds only
the recorded named function. A stale FactId or changed reduced object is a
compiler error; the compiler never scans available definitions for another
route.

One local source statement may establish several facts. Therefore the local
composition function returns ordered Lean proof lines rather than pretending
that every proof step has one output. A reused branch-component FactId is an
alias in the current compiler environment, while a newly stored proof-step
FactId is installed from its own store Result. This distinction is determined
by the recursive Result effects together with the facts already visible in the
current compiler environment; it never allocates a replacement FactId.

The compiler dispatcher does not create a node. It only selects one of these
composition actions:

- compile a leaf from typed evidence;
- wrap one recursively compiled child;
- combine several named or ordered children;
- pass a child through unchanged;
- resolve an exact `FactId`/shared-result reuse.

This is why no enum mirroring every Rust helper or every compiler function is
needed.

## Every Function Has a Composition Mode

Not every `exec_*` or `verify_*` function needs a new enum variant. A function
instead has one of five composition responsibilities:

| Mode | Result behavior | Typical use |
| --- | --- | --- |
| `Leaf` | Construct a result from a checked primitive fact or computation. | A closed numeric membership rule records its evaluation certificate. |
| `Wrap` | Retain one exact child and add one semantic transformation layer. | `SuccessTransformFactResult` wraps the previously proved source fact and the selected rewrite rule. |
| `Combine` | Retain several named or ordered child results. | `exec_fact` combines well-definedness, proof verification, store, and inference. |
| `PassThrough` | Return the exact child unchanged. | A dispatcher that only selects a fact family does not invent a proof layer. |
| `Reuse` | Cite an earlier shared proof node. | Statement memoization and object-WD caches return an `Rc` source instead of cloning or flattening it. |

This classification follows semantic work, not function names or call-stack
depth. A helper that only dispatches is `PassThrough`; a helper that proves a
new obligation is `Leaf`, `Wrap`, or `Combine`. Consequently, refactoring a
Rust helper does not automatically change the stable result schema.

`DefSettingStmt` is a statement-level `PassThrough` without a child. A setting
only guides Litex elaboration; every later use has already become ordinary
fresh binders and premise facts in that later statement's Result. The compiler
therefore checks that `SuccessDefSettingStmtResult` has no mathematical
effects and emits no Lean declaration or environment binding. Keeping a
setting table in the compiler would duplicate parser state and would violate
the rule that compiler environments contain only names needed by generated
Lean scopes.

Child results are never flattened into a generic `inside_results` list.
Statement-specific fields state what each child means: `proof_steps`,
`branches`, `requirements`, `premises`, `conclusions`, `well_definedness`,
`verification`, `store`, and so on. Consumers therefore do not infer roles
from vector lengths, source strings, or traversal positions.

## Fact Statement Composition

[`exec_fact`](../execute/exec_fact_stmt.rs) makes the three major fact stages
explicit:

```rust
let well_definedness = self.exec_fact_stmt_verify_well_definedness(fact)?;
let result = self.exec_fact_stmt_verify_process(fact)?;
let infers =
    self.exec_fact_stmt_affect_environment(fact, &result, &well_definedness)?;

Ok(result
    .with_fact_well_definedness(well_definedness)
    .with_infers(infers))
```

The final fact result owns all three:

```rust
pub struct SuccessFactStmtResult {
    pub verification: Rc<SuccessVerifyFactResult>,
    pub well_definedness: SuccessVerifyFactWellDefinedResult,
    pub store: SuccessStoreFactResult,
    pub execution_trace: Option<StatementExecutionTrace>,
}

pub struct SuccessStoreFactResult {
    pub fact: Fact,
    pub fact_id: Option<FactId>,
    pub infers: SuccessInferResult,
}
```

`SuccessVerifyFactResult` recursively mirrors the semantic split of `Fact`:
atomic, existential, disjunction, conjunction, chain, universal, universal
iff, and negated universal. Each proof node then records the successful proof
route in `SuccessFactProofResult`, for example a builtin certificate, an exact
`FactId` citation, a known-forall instantiation with checked requirements, a
combined proof, a transformation, or an exact shared reuse node.

Diagnostic labels remain available for human output, but the target design is
that they are not semantic compiler input. New compiler-ready builtin routes
carry a typed `BuiltinRuleEvidence` payload whose target and children validate.
The temporary compatibility adapter still has an allowlisted label-and-goal path
for older builtin routes; that transitional boundary is recorded below and
must not be used for new routes.

## Well-Definedness, Binder Scope, and Identity

Well-definedness is part of the returned result rather than a separate
compiler lookup. The structures are defined in
[`success_well_defined_result.rs`](../result/success_well_defined_result.rs).

An object WD result is either:

- `Direct`, which owns the constructor-specific child checks;
- `Reuse`, which cites the exact earlier `Rc` proof node; or
- `RecursiveReference`, which records reviewed recursive re-entry.

A direct result owns named collections such as child objects, fact checks,
target requirements, stores, and an optional binder result. Binder scope is
represented by ordinary recursive ownership. For example, a forall WD result
owns its parameter groups, premises, and conclusions; a set-builder WD result
owns its parameter premises and body conditions. A local result is therefore
nested below the binder that makes it meaningful.

There is no canonical `ScopedBinderIr`, `ScopedFactIr`, or per-fact vector of
ambient binder IDs. The tree structure is the scope structure. This remains
valid even when execution used `run_in_local_env`: the local runtime may be
popped, while its owned `Box`, `Vec`, and `Rc` results remain inside the parent
result.

Identity has two distinct forms:

- Cross-statement and stored-fact references use the exact `FactId` assigned
  while the relevant environment is alive.
- Sharing inside one returned proof/WD DAG uses an exact `Rc` source through a
  `Reuse` node.

Inside the canonical Result, neither identity is recovered by
proposition-string lookup. A repeated proposition may have a different
`FactId`, while a memo/cache hit must point to the exact earlier proof node.

## Worked Example: `2 + 3 $in N`

The persistent tracer is
[`examples/03_language_features/compositional_stmt_result.lit`](../../examples/03_language_features/compositional_stmt_result.lit):

```litex
2 + 3 $in N
```

Before the compositional Result design, the numeric verifier retained only a
diagnostic such as `number in N`. The temporary computation `2 + 3 -> 5`, WD
children, store identity, and inference route were not all available as one
returned structure.

The completed result now has this schematic shape. Names and ownership match
the Rust structures; line metadata and secondary inference effects are elided:

```text
StmtResult::Success
  SuccessStmtResult::Fact
    SuccessFactStmtResult
      well_definedness
        AtomicFact: 2 + 3 $in N
          argument 0: 2 + 3
            Direct WD
              child 0: 2
              child 1: 3
              target requirement: 2 $in C
              target requirement: 3 $in C
          argument 1: N
            Direct WD
          predicate
            name: in
            expected_arity: 2
            domain_checks: []

      verification
        AtomicFact: 2 + 3 $in N
          BuiltinRule
            evidence: ClosedNumericMembership
              expected_target: 2 + 3 $in N
              target_set: N
              evaluation
                expression: 2 + 3
                value: 5
                step: Binary(Add)
                  left
                    expression: 2
                    value: 2
                    step: Literal(2)
                  right
                    expression: 3
                    value: 3
                    step: Literal(3)

      store
        fact: 2 + 3 $in N
        fact_id: F_source
        infers
          rule: NaturalMembershipImpliesNonnegative
          premises
            - fact_id: F_source
              fact: 2 + 3 $in N
          conclusions
            - fact_id: F_nonnegative
              fact: 2 + 3 >= 0

      execution_trace
        verify_well_definedness: success
        verify_process: success
        affect_environment: success
```

The source proposition remains `2 + 3 $in N`; normalization does not replace
it with `5 $in N`. Instead, the selected builtin proof owns the exact recursive
evaluation certificate that connects the source expression to `5`. The store
node owns the source `FactId`, and the typed inference application cites that
same ID as the premise of the nonnegativity conclusion.

This is enough for the Result-to-Lean compiler to construct proof terms along
the same route:

```lean
theorem __fact0 : Litex.In ((2 : ℂ) + (3 : ℂ)) Litex.N := by
  exact Litex.Rules.complexEqNatInN
    ((2 : ℂ) + (3 : ℂ)) 5 (by norm_num)

theorem __fact1 : Litex.Nonnegative ((2 : ℂ) + (3 : ℂ)) := by
  exact Litex.Rules.nonnegativeOfInN (__fact0)
```

Here `norm_num` is not target-side proof search for membership. It appears
inside the fixed `complexEqNatInN` adapter only after Litex has selected and
returned the exact closed evaluation certificate with normal value `5`. The
second theorem is not reproved independently: its result came from the typed
inference edge whose premise is the stored membership fact.

## Finite Proof Methods as Nested Result Composition

`by extension`, `by enumerate finite_set`, and `by for` demonstrate three
levels of the same model. `by extension` owns two ordered directional child
Results. A directional proof step may itself be a finite enumeration Result;
that Result owns an ordered assignment Result for each resolved element. No
separate scope IR is needed: the Rust field nesting is the lexical nesting.

Integer-range iteration does not retain a string such as `"ranges"`. It uses
named Result structures:

```rust
pub enum SuccessVerifyByForResult {
    Ranges(Box<SuccessVerifyByForRangesResult>),
    CartesianProductOfListSets(
        Box<SuccessVerifyByForCartesianProductOfListSetsResult>,
    ),
}

pub struct SuccessVerifyByForRangesResult {
    pub parameters: Vec<SuccessVerifyByForRangeParameterResult>,
    pub prove_goal: String,
    pub assignments: Vec<SuccessVerifyByAssignmentResult>,
    pub generated_forall: String,
}

pub struct SuccessVerifyByForRangeParameterResult {
    pub parameter: String,
    pub range: ClosedRangeOrRange,
    pub evaluated_start: String,
    pub evaluated_end: String,
    pub enumerated_values: Vec<String>,
}
```

For `forall n range(0, 3): n < 3`, the parameter Result retains the exact
source range, evaluated endpoints `0` and `3`, and ordered values
`[0, 1, 2]`. Each assignment Result owns the local `n $in Z` FactId, the exact
`n = value` FactId, their inference children, domain checks, proof-step
Results, and conclusion checks. The compiler validates the complete wrapper,
pushes one inherited environment per assignment, installs only that
assignment's identities, compiles the children, and pops the environment.
Runtime-resolved numeric comparison evidence is accepted only inside this
exact assignment wrapper, where the native range equality is structurally
owned; the same evidence outside such a wrapper still fails closed.

The persistent examples are
[`50_SetExtensionResultComposition.lit`](../../lean/examples/50_SetExtensionResultComposition.lit),
[`51_FiniteEnumerationResultComposition.lit`](../../lean/examples/51_FiniteEnumerationResultComposition.lit),
and
[`52_IntegerRangeIterationResultComposition.lit`](../../lean/examples/52_IntegerRangeIterationResultComposition.lit).
Each has a paired generated Lean file checked by Lean itself. Corruption tests
change assignment FactIds or evaluated range values and require compilation to
fail before source is emitted.

Set-builder inference follows the same contract. A successful
`value $in {x S: P(x)}` Result records one
`SetBuilderBaseMembershipProjection` and then one
`SetBuilderPredicateProjection { clause_index }` for every defining clause.
Each node cites the source membership `FactId` and owns the projected fact's
`FactId`. The compiler can therefore emit the base and clause projections in
their retained order without searching stored propositions or reconstructing
the clause index.

Registered set builtins follow the same contract. A direct compiler layer
validates the retained `RuleId`, semantic fingerprint, target-matched bindings,
parameter checks, and ordered semantic child Results. Only then does it
construct the corresponding `Litex.SetRules` proof in the current compiler
environment. The registry certificate is semantic Result input, not a
diagnostic label and not a request to rerun verifier search.

Registered sign and strict-to-weak order rules use the same layer. The
compiler reads only the generated registry fingerprint metadata for the
retained `RuleId`; it does not parse a rule schema or run its matcher again.
The target-specific compiler method then checks the exact real-valued
bindings, parameter requirements, target operands, and ordered child Results
before constructing the Lean rule application. Ordinary typed
`BuiltinRuleEvidence::Arithmetic` sign rules share the same target-side
constructor after their own Result shape has been validated.

Integer remainder demonstrates a target representation that legitimately
belongs in the compiler environment stack. Runtime returns
`IntegerMembershipClosure::Mod` with one conjunction child proving the left
and right operands are in `Z`. While compiling a binder, the corresponding
membership proofs select exact Lean `ℤ` representatives and install
`SymbolId -> integer representative` only in that lexical compiler frame. The
remainder layer validates both ordered membership components, recursively
checks the conjunction proof, computes `%` on those representatives, casts the
result to the ordinary Complex observation, and applies
`Litex.Rules.complexIntInZ`. It neither invents a Complex remainder operation
nor stores integer membership truth in the compiler environment.

Rational integer power uses the same separation. Its conjunction child proves
`base ∈ Q` followed by `exponent ∈ Z`. The active frame maps the two binder
`SymbolId`s to the exact `ℚ` and `ℤ` representatives selected by those visible
membership proofs. The power layer validates the two child facts in order,
constructs native rational `base ^ exponent`, casts that value to the Litex
complex observation, and applies `Litex.Rules.complexRatInQ`. Both target
representations vanish with the enclosing forall frame; neither is a new
proof fact or an alternative execution environment.

Typed order transitivity is a larger `Combine`. Its leading children are the
verifier-owned numeric carrier checks; its final two children are the ordered
comparison path. The compiler validates that the first left endpoint is the
target left, the middle endpoints coincide, the second right endpoint is the
target right, and at least one premise is strict when the target is strict.
It then selects only the corresponding fixed `Litex.Le`/`Litex.Lt`
transitivity constructor. Child order is semantic data, not display order.

Order reflexivity and closed numeric comparison are deliberately different
leaf Results. `x <= x` owns
`OrderReflexivityBuiltinRuleEvidence { expected_target, repeated_object }` and
is compiled as `Litex.Le.refl x` while the enclosing forall Result's compiler
environment is active. `2 + 3 < 6` owns
`ClosedNumericComparisonBuiltinRuleEvidence` with separate left and right
`SuccessEvaluateObjResult` children; the left child records the recursive
`2 + 3 -> 5` computation. A `RuntimeResolvedNumericComparison` is retained for
execution when verification substitutes environment values. The compiler
accepts it only when enclosing successful definition or finite-assignment
Results have already installed the exact source bindings in the current
compiler environment frame. It recomputes both retained normal forms through
those bindings and rejects a mismatch rather than asking the execution Runtime
to rediscover one.

[`53_RuntimeResolvedComparisonFromDefinitionResults.lit`](../../lean/examples/53_RuntimeResolvedComparisonFromDefinitionResults.lit)
is the persistent definition example. Its two definition Results publish
`a = 1` and `b = 2` to the compiler environment stack. The following fact
Result retains `0 <= a + b`, the runtime normal forms `0` and `3`, source
storage, and the typed inference deriving `-1 * (a + b) <= 0`. Lean lowering
uses the source FactId in
`complexNegativeOneMulNonpositive`; it does not prove the inferred fact again
with an unrelated numeric tactic. The target ABI therefore represents the two
zero-ended directions symmetrically as `Nonnegative x` for `0 <= x` and
`Nonpositive x` for `x <= 0`.

Exact `FactId` citation remains a separate compiler layer. Litex permits dual
surface spellings such as `a >= 0` and `0 <= a`. A citation may pass through
that layer unchanged only when the verifier-retained source and target are the
exact comparison-notation duals and both render to the identical Lean
proposition. This is a checked `PassThrough`, not proposition lookup: the Lean
proof name still comes exclusively from the retained source `FactId` in the
current compiler environment.

Known-forall instantiation is a direct `Combine` above those two layers. Its
Result retains the source forall `FactId`, ordered argument objects, and one
recursive Result for every parameter-type and domain requirement. The compiler
resolves the source theorem in its current environment, compiles those child
proofs in order, performs stateless source-syntax substitution to check the
single instantiated conclusion, and emits the Lean application. It never asks
the execution Runtime which forall might prove the target. This application
does not introduce a lexical scope; a separate forall-introduction Result owns
the binder body and therefore owns the corresponding compiler-environment
push/pop.

Basic forall introduction is now that direct lexical `Combine`. The compiler
projects the one parent-owned recursive WD tree only as a temporary rendering
view, pushes one inherited compiler environment, and keeps that view active for
the complete binder frame. Each parameter then installs its exact `SymbolId`
and stored premise `FactId`; function parameters also install the exact
membership contract consumed by nested applications. A source `A set` check is
validated but creates no separate Lean proof term because the generated binder
already has type `A : Litex.Set`. Heterogeneous object and function parameters
introduce their generated carrier binder before the source value and membership
hypothesis.

Each ordered conclusion proof reads the matching
`SuccessVerifyForallFactWellDefinedResult::conclusions[index]` child while the
same binder environment is active. Multi-layer function calls can therefore
follow parent-owned `FunctionPrefix` edges such as `g(a)(b) -> g(a)` without
inventing a parser occurrence ID for the verifier-generated prefix. The local
conclusion FactIds disappear when the environment is popped, but the compiler
retains their typed projection bindings to the emitted outer Lean theorem. A
forall statement may intentionally have no outer `FactId`; in that case the
outer no-ID store Result is validated, one Lean theorem is emitted, and only
the exact conclusion FactIds are published to later compiler layers. Explicit
domain premises whose stores introduce no additional inferred facts use the
same environment: their ordered store FactIds are installed after the
parameter FactIds, remain visible to every conclusion
child, and are retained as premises of the conclusion projection after the
local frame is popped. Refined-set binders use that binder frame too; their
exact nonempty/finite property FactIds are installed alongside ordinary set
parameters. Domain/parameter stores with additional
assumption-inference children remain the next forall-introduction tranche.

The focused direct-compiler and corruption regressions live in
[`stmt_result_to_lean_compiler.rs`](stmt_result_to_lean_compiler.rs), and the generated Lean assertions live in
[`stmt_result_to_lean_compiler_tests.rs`](stmt_result_to_lean_compiler_tests.rs).

## Strategy Definition as a Result-Owned Compiler Environment

A verified strategy demonstrates why the compiler environment stack follows
Result fields rather than Rust call depth. Its successful verification result
is explicit:

```rust
pub struct SuccessVerifyStrategyDefinitionResult {
    pub name: String,
    pub forall_fact: ForallFact,
    pub well_definedness: SuccessVerifyFactWellDefinedResult,
    pub proof_scope: SuccessVerifyLocalProofScopeResult,
    pub proof_steps: Vec<StmtResult>,
    pub conclusion_checks: Vec<StmtResult>,
}
```

The enclosing `SuccessDefStrategyStmtResult` owns the final outer store. The
fields above own the inner verification procedure. Compilation therefore has
one direct structural flow:

```text
SuccessDefStrategyStmtResult
  -> validate recursive forall well-definedness
  -> push inherited compiler environment for proof_scope
       -> install parameter and premise FactIds
       -> compile proof_steps in source order
       -> compile conclusion_checks in source order
  -> pop compiler environment
  -> emit the proved forall as a Lean theorem
  -> publish only the outer stored forall FactId
```

The theorem and strategy statement families share this shape through
`NamedForallStatementResultCompilationInput`. That type is only a borrowed
compiler function argument: every field points into the canonical Result, so
it is not a second IR and owns no copied proof data. A missing local parameter
store, wrong FactId, changed conclusion, or reordered child is rejected before
Lean source is published.

Strategy activation has no Lean analogue. The successful definition proves
and stores the forall theorem; later `use strategy` and `stop strategy` affect
only Litex Runtime proof search. Their Results validate as pass-through layers
and emit no declaration. The persistent example is
[`43_StrategyDefinitionCompilerEnvironment.lit`](../../lean/examples/43_StrategyDefinitionCompilerEnvironment.lit).

## Why There Is No Full Mirrored Statement IR

`SuccessStmtResult` already is a typed, recursive source tree. Constructing a
second compiler-only statement tree with the same statement variants and the same
proof nesting adds copying and creates two places that can disagree. The
target architecture therefore compiles Result directly.

Small target-side helper structures are still legitimate when they describe
a real Lean-only choice—for example a generated binder name or the native Lean
representation selected for one Litex object. They are compiler environment
bindings, not another statement/proof tree. They must not rediscover a rule,
FactId, premise, scope, or normal form that Result was responsible for
returning.

An unsupported object, statement, proof rule, WD shape, missing evidence
payload, or dangling `FactId` causes compilation to fail closed, never a
guessed proof or `sorry`. The numeric tracer above is already on the direct
path: it validates the recursive WD and evaluation Result, uses the source
FactId, follows the typed infer edge, and creates no old statement/fact IR.

This separation also preserves the Litex execution contract: a Litex program
may execute successfully even when the Lean backend does not yet implement
its result shape. Compiler support is narrower than kernel execution support.

## JSON v2 and Result Graphs

The ordinary CLI renders the recursive Result directly through
[`result_json_v2.rs`](../output/result_json_v2.rs) with schema
`litex.statement-result.v2`. It does not first project the result back into the
old flattened output model. Shared `Rc` nodes receive stable local `$id`
references so a DAG remains finite in JSON.

The result graph in
[`result_graph.rs`](../graph/result_graph.rs) is another read-only projection
of the same structure. Statement nesting comes from named result fields;
dependency edges come from `FactId` citations and exact shared nodes. The
graph is a presentation format, not an input to verification or compilation.

Neither JSON nor graph serialization sits on the compiler path. The compiler
consumes the Rust Result structures directly.

## Current Boundaries

- The migration preserves existing Litex execution behavior. It does not add
  a new statement transaction model or an Error Result tree.
- Unknown and failed statements are never lowered to Lean.
- Not every existing builtin or inference route carries a compiler-ready typed
  certificate yet. Litex execution may succeed while Lean lowering rejects
  that route.
- There is no compatibility builder, mirrored statement/proof tree, or
  diagnostic-label-to-rule fallback. New compiler support must consume typed
  Result evidence directly rather than reintroducing one of those paths.
- The compiler may keep short-lived target representations and lexical lookup
  indexes. They describe Lean spelling and visible names; they are not a
  second semantic tree and may not replace exact `FactId` citations with
  proposition lookup.
- Missing `FactId` and execution-trace attachment happens at the statement
  boundary while the runtime is still alive. Already frozen local FactIds are
  never overwritten by a later ambient fact with the same proposition. After
  `exec_stmt` returns, the Result is self-contained for JSON, graph, and
  compiler consumers.
- Lean-source construction may use tactics only inside reviewed fixed adapters
  after validating verifier-owned evidence. It may not launch open-ended
  target-side proof search.
- Generated Lean must contain no compiler-invented axioms, `sorry`, or
  resurrection of the deprecated universal `LitexObject` representation.

Example 54 adds exact complex algebraic normalization. The verifier returns a
typed `ComplexAlgebraicNormalization` certificate containing the exact target
and the ordered nonzero premises required by every division or negative power.
The compiler independently reruns the bounded normalizer, reproduces that
premise list, consumes the corresponding child Results (including frozen
FactId citations for ambient premises), and bridges each semantic disequality
to native Complex nonzero before using a fixed
`field_simp`/`ring_nf`/`norm_num` adapter. Literal integral powers fall back to
native Complex exponentiation only when the existing exact-rational power
representation is unavailable. A missing symbolic nonzero premise still fails
in Litex well-definedness rather than becoming target-side proof search.

The persistent compiler examples currently extend through
[`54_ComplexAlgebraicCalculation.lit`](../../lean/examples/54_ComplexAlgebraicCalculation.lit).
They exercise the direct Result reader and compiler environment stack; they do
not claim that every statement accepted by the full Litex kernel is already a
supported Lean target.
