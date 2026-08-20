# The Two Hard Problems in the StmtResult-to-Lean Compiler

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

# Representation of Litex Mathematics in Lean

# Turn Litex Kernel Execution Information into Lean Proofs

## Design Goal

The compiler does not ask Lean to rediscover why a Litex statement succeeded.
Litex execution returns one recursive, typed result that records the successful
route from its leaves to its statement root. The compiler consumes that result
and deterministically replays the selected route as Lean declarations and
proof terms.

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
`LitexToLeanStatementIr::HaveObjEqualStmt` node. Checked set aliases use the
same parent Result to install their names in a child compiler environment, so
leaving a `sketch` removes those bindings automatically.

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

The matching `obtain y from exist ...` elimination reads the recursively
retained source fact Result and resolves its exact `FactId`. It validates the
source existential binder in a temporary compiler environment, then discards
that template-only environment. The environment visible to following Results
contains only the selected Lean object `y` and the two exact projection
FactIds: the witness-type fact and the instantiated body fact. Their Lean
proofs are the corresponding projections of `Classical.choose_spec`; no
proposition-string search and no live `Runtime` lookup is involved.

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

The focused direct-compiler and corruption regressions live in
[`stmt_result_to_lean_compiler.rs`](stmt_result_to_lean_compiler.rs), and the generated Lean assertions live in
[`stmt_result_to_lean_compiler_tests.rs`](stmt_result_to_lean_compiler_tests.rs).

## Why There Is No Full Mirrored Statement IR

`SuccessStmtResult` already is a typed, recursive source tree. Constructing a
second `LitexToLeanStatementIr` with the same statement variants and the same
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
- [`builder.rs`](../litex_to_lean_ir/builder.rs) is a temporary compatibility
  adapter for statement/proof families not yet moved to direct Result
  traversal. It still contains a legacy
  `try_from_verified_builtin_label` fallback for an allowlisted set of older
  builtin routes. New routes must return typed evidence; removing this fallback
  requires migrating each remaining producer first.
- The canonical WD Result owns binder scope recursively, but
  [`compositional_well_definedness_projection.rs`](../result/compositional_well_definedness_projection.rs)
  currently projects it into the older Lean-backend certificate with allocated
  WD node IDs and ambient scope paths. Those IDs are backend-local and are not
  canonical statement-result identity. The compiler environment holds this
  compatibility view only while an unmigrated object renderer constructs one
  proposition or proof term, then restores the surrounding frame. New compiler
  paths read the recursive WD Result directly and must not add another
  persistent scope-ID table.
- The compatibility adapter still keeps a rendered-proposition index for a few local
  already-stored effects. Canonical citations carry `FactId`; the remaining
  index is a backend migration debt and must not be extended as an identity
  mechanism.
- Missing `FactId` and execution-trace attachment happens at the statement
  boundary while the runtime is still alive. Already frozen local FactIds are
  never overwritten by a later ambient fact with the same proposition. After
  `exec_stmt` returns, the Result is self-contained for JSON, graph, and
  compiler consumers.
- Lean-source construction may use tactics only inside reviewed fixed adapters after
  validating verifier-owned evidence. It may not launch open-ended target-side
  proof search.
- Generated Lean must contain no compiler-invented axioms, `sorry`, or
  resurrection of the deprecated universal `LitexObject` representation.
