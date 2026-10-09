# Litex-to-Lean Compiler Implementation

This module compiles the completed typed execution result into Lean source.
The [compiler guide](../../docs/Litex_To_Lean_Compiler_Guide.md) explains source
semantics and examples; [CLI documentation](../../docs/cli.md#lean-compiler-boundary)
owns invocation and output behavior.

## Public entrypoint

```rust
let result = runtime.run_litex_code(&source)?;
let compiler = LitexToLeanCompiler::new(runtime);
let lean = compiler.compile_run(&result, &namespace)?;
```

The compiler owns only the original `Runtime`, moved into it after source
execution without cloning. It has no lifetime parameter or result field.
`compile_run(&self, result, namespace)` receives the completed run as a method
input and reads Runtime only for exact citation resolution. Branch methods
likewise receive their original typed results as parameters. Reusing the same
compiler does not retain an earlier result or partial output.

The free `compile_run(result, runtime, namespace)` convenience function also
takes ownership of Runtime; its previous borrowed-Runtime signature has changed.
The CLI executes source once, transfers Runtime into the compiler, and returns
the complete artifact only after every statement is compiled.

## Result dispatch and file ownership

The layout mirrors `src/execute`: one dispatcher per existing result enum and
separate files/folders for its mathematical branches. Methods belong to the
same `LitexToLeanCompiler`; there are no mutable child compilers or parallel
compiler result types.

```text
RunLitexCodeResult.statement_results
  -> ExecStmtResult
     -> ExecDefinitionStmtResult -> ExecDefineObjStmtResult / DefThm
     -> ExecByStmtResult -> ByThm
     -> ExecFactStmtResult -> VerifyFactResult
        -> equality / atomic-except-equality / forall
        -> selected searched_proof and its original children
        -> object WD and its original constructor/domain evidence
```

The entrypoint owns run validation, namespace/header output and ordered traversal.
Statement dispatch belongs to `compile_stmt_result`; leaf owners mirror let,
have, theorem, by-theorem and fact-result branches. `source_position` reads the
original result prefix/ancestors; `source_queries` resolves exact subjects.
`compile_store_result` validates actual stores. Naming helpers spell existing source IDs;
`lean_compile_error` reports source statement position and rejected route.

## Borrow the source tree; generate temporary output

No persistent ObjectTerm, NumericTerm, FactTerm, NamedTheorem, OutputReference,
EmittedFact, ContextParameter or output-scope registry is needed. Original
parameters, facts, stores and selected proofs remain in the source results.
Children return temporary Lean expressions; a proof renderer can return a
proposition and proof string without copying the source fact.

A source-position cursor contains only borrowed original result owners, parent
positions and the current stage/child boundary. It identifies which source
prefix is being compiled. For example, left-operand WD can be available before
right-operand cached WD, while the statement's truth proof is still unavailable.
It is neither another ExecEnv nor an object/fact/proof cache.
Its internal borrow lifetime remains explicit where Rust requires it; this
does not impose a lifetime parameter on the owning compiler API.

Each source proof is named `h_<original FactId>`, including exported facts,
named theorems, local hypotheses, stored alias equalities, supported inference
and theorem-return projections. Declarations and citations use the same actual
ID; statement positions determine traversal order, not proof names. Producers
are emitted at their actual stage. Temporary Verify children are not
automatically stored facts; some obligations reuse the owning target FactId.
Their selected proofs may be passed directly to certified constructors.

A declaration's parameters come from its original source position. Introducing
another object later cannot extend an earlier theorem's signature. Generic
hosts retain their own universe, Representation, certified Obj and ordinary
membership hypothesis. Universes and parameter strings are rendered from
source records, not retained in parallel compiler lists.

Some constructor types refer to an earlier local membership or domain proof.
When that proof name occurs in an exported proposition, close the proposition
over the necessary actual producer definitions as ordered Lean `let` values.
These are proof expressions, not additional assumptions. Unused definitions
are omitted, and the ordinary theorem statement remains definitionally equal
to the source proposition.

## Exact citation and scope checks

Lookup reads earlier siblings and active source ancestors. At root, earlier
exported statements are visible; their closed theorem/forall/call bodies are
not. In a local result, only introductions, assumptions and completed stages
are visible. Future siblings and later stages are unavailable.

Captured `local_env` and Runtime resolve exact FactId/WdId subjects only. A
resolved subject is insufficient: a supported source producer must also occur
in the visible original prefix. This preserves rejection of removed producers,
future references, wrong subjects and closed-scope citations even if Runtime
still holds a matching record. Unsupported inferred facts never become new
hypotheses.

Current results are not a standalone citation closure. Let retains stored IDs
rather than the full store/infer result, and anonymous ByDef WD does not retain
its later cache-registration ID. Root references also use live Runtime. Any
Runtime-free compilation requires an explicit producer-capture design; it must
not be simulated with a new compiler-owned store.

## Mathematical adapters and support boundary

Every object owns WD. Constructor compilation replays certified children and
exact membership/nonzero/domain proofs before truth evidence. Arithmetic keeps
Litex construction shape. Membership adds knowledge without choosing a new
host type for a generic object.

Numeric denotation, C/R-membership and closed-value evidence are rendered by
leaf helpers from actual source constructions and selected proofs. Removing a
numeric cache does not remove these semantic bridges or authorize recovering
a proof by target-shape matching.

Selected adapters include reflexivity, exact closed calculations, recorded
rational normalization, scalar division relations, arithmetic congruence,
equality paths, membership transport, supported numeric hierarchy and real
order routes. Fixed `ring`/guarded normalization checks the source-selected
certificate family; no independent target theorem search is performed. The
source Rational tag does not contain a monomial trace, so Lean checks the
normalization proof rather than replaying an unavailable low-level trace.

The accepted mathematical profile remains phases 1 and 2: numeric N/Z/Q/R/C,
selected real comparisons, top-level numeric contexts, let/typed-have aliases,
named theorems and explicit returned-atom selection. Owned functions/prop,
sets, local arbitrary-have, general consumed inference and module compilation
retain explicit unsupported branches. Exact certificates, orientations,
argument match evidence and residual children must be preserved.

A compound constructor recorded only inside a closed theorem-call scope is
not a parent-scope WD producer. A nested call whose enclosing conclusion lacks
that producer still rejects with `WD/Producer`. The positive nested-call
regression constructs the object in an earlier parent proof step; the bare
call remains a source-capture gap, not a newly supported route.

Any failed source, unsupported branch or unavailable evidence rejects the
entire artifact. No partial Lean file, new axiom, proof hole or fabricated
premise is emitted.

## Verification

```sh
cargo test --release --lib compile_to_lean::tests
python3 scripts/litex_to_lean/check.py
```

Rust tests check actual result contracts and corrupt/deleted producer controls.
The local gate separately runs strict source verification, actual CLI generation,
byte-for-byte pair drift, pinned Lean warnings-as-errors, negative controls and
native consumers. Canonical pairs belong in `lean/examples`; all check tooling,
receipts, Lake/dependencies, native adapters and drafts stay in ignored
`scripts/litex_to_lean`. Generated Lean files are changed only through the CLI.
