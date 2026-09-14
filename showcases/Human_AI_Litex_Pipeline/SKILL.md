# Litex + AI Loop

Use this skill to help a user construct checkable mathematics with Litex and AI. It applies to a single definition, one theorem, a proof repair, a reusable mathematical interface, a textbook chapter, or a multi-file theory. It is not tied to any mathematical subject or example.

The outcome is not merely Litex code. A successful loop produces:

1. a human-owned mathematical contract;
2. a dependency-ordered mathematical development;
3. a JSON record of verifier-backed attempts and decisions;
4. materialized `.lit` source containing only accepted mathematics;
5. an honest verification and trust-boundary report; and
6. when explicitly in scope and supported, a Lean artifact checked by Lean's kernel.

## First principles

Keep five sources of truth separate:

| Concern | Authority |
|---|---|
| What the mathematics is intended to mean | The user and the cited mathematical source |
| What candidate should be tried next | The AI agent |
| Whether the candidate is checkable | The Litex verifier |
| Why the work moved from one candidate to the next | The JSON proof journal |
| What constitutes the maintained mathematical development | The materialized `.lit` source |

These ownership boundaries imply the following rules:

- Never change a definition, theorem statement, quantifier, carrier, assumption, or scope merely to make verification easier. Surface that semantic choice to the user.
- Treat AI output as a proposal. A plausible explanation or proof is not checkable until Litex accepts it.
- Treat verifier feedback as a state transition, not as prose decoration. A failed transaction must not damage the accepted prefix.
- Keep attempt history and debugging evidence in JSON. Keep the final `.lit` source mathematical and reader-facing.
- Treat verification as necessary but not sufficient. A verified proof may still contain redundant facts, accidental interfaces, or an avoidable representation detour.
- Report every `trust`, `abstract_prop`, assumed interface, unverified import, and checker boundary. Do not call a development `checkable` while unresolved trust remains.

## New-pipeline result-shape contract

When working on `src/new_pipeline`, make the return types expose the function's
actual control flow. There are two distinct shapes:

### Sequential pipelines use result structs

If a function must complete several ordered stages, define a dedicated result
struct whose fields appear in that same order. Each field contains the typed
output of one stage.

For example, a atomic-except-equality atomic-fact verifier that performs
well-definedness first and proof search second has this shape:

```rust
pub struct VerifyAtomicExceptEqualityFactResult {
    pub verify_well_defined_result: VerifyAtomicFactWellDefinedResult,
    pub searched_proof: AtomicExceptEqualityFactSearchedProof,
}
```

The implementation must preserve the same dependency order:

```rust
let verify_well_defined_result =
    self.verify_atomic_fact_well_definedness(fact, state.clone())?;
let searched_proof =
    self.search_atomic_except_equality_proof(fact, state)?;
Ok(VerifyAtomicExceptEqualityFactResult {
    verify_well_defined_result,
    searched_proof,
})
```

Use a field named `...WellDefinedResult` when the stage may expose cache hits,
definition paths, identifiers, or other execution evidence. Use
`...WellDefinedProof` only for a pure proof object. The outer
`Result<T, RuntimeError>` represents operational failure; a successfully
returned `T` represents a completed pipeline. Do not encode a failed stage as
a successful status variant. Retain the input subject in the result only when
the result is cached, rendered, persisted, or otherwise consumed after the
call's input is gone.

Use a direct struct field when every child must be proved, such as:

```rust
pub struct VerifyAndFactResult {
    pub verify_well_defined_result: AndFactWellDefinedResult,
    pub proof_of_each_conjunct: Vec<VerifyFactResult>,
}
```

Use a nested search enum when the stage chooses exactly one mutually exclusive
route. `searched_proof` means the selected successful route; a future record of
all failed attempts belongs in a separate `search_trace` field.

### Dispatchers use recursively mirrored enums

If a function dispatches on an input enum, its result enum must mirror that
enum, recursively. Every constructor calls a dedicated branch function and
stores that branch's dedicated result type:

```rust
pub enum ExecStmtResult {
    Fact(ExecFactStmtResult),
    Definition(ExecDefinitionStmtResult),
    Unsafe(ExecUnsafeStmtResult),
}

pub enum ExecDefinitionStmtResult {
    LetObj(ExecLetObjStmtResult),
    DefProp(ExecDefPropStmtResult),
}
```

The same rule applies to verification dispatchers:

```rust
pub enum VerifyAtomicFactResult {
    Equality(VerifyEqualityFactResult),
    AtomicExceptEquality(VerifyAtomicExceptEqualityFactResult),
}

pub enum VerifyExistFactResult {
    Plain(VerifyPlainExistFactResult),
    Unique(VerifyExistUniqueFactResult),
    NotExist(VerifyNotExistFactResult),
}
```

Do not flatten branch-specific data into one generic struct. Do not use a
wildcard branch in the final dispatcher: exhaustive matching should reveal
every unconnected AST constructor. An explicit `Unsupported` error may be a
temporary tracer-stage bridge, but it must not hide missing final branches.

Apply the rule at every level: `Fact -> VerifyFactResult`,
`AtomicFact -> VerifyAtomicFactResult`, and `Stmt -> ExecStmtResult` should
form the same shape tree as their input enums. Reserve successful `Unknown`
variants for a real domain outcome; inability to produce a proof normally
belongs in the error path.

## The loop is a state machine

Do not treat “using AI” as a label for code generation. Assign one authority to each decision and preserve the state transition that connects them:

| Participant or artifact | Authority | Must not substitute for |
|---|---|---|
| Human | Mathematical intent, constraints, semantic choices, and acceptance scope | Litex's checking decision |
| AI | The next candidate fact, proof block, dependency plan, or evidence-backed repair | Mathematical intent or verifier acceptance |
| Litex | Whether a candidate is well defined and supported by the available evidence | The human's judgment about intended meaning |
| JSON journal | The inspectable proposal, machine result, diagnosis, and next repair | The verifier or canonical mathematical source |
| Materialized `.lit` | The maintained contiguous prefix of committed mathematics | Attempt history |
| Litex-to-Lean compiler and adapter | A supported evidence-preserving handoff when requested | Proof evidence that the route does not support |
| Lean kernel | The final checking decision for an actually generated Lean artifact | Litex verification or an AI explanation |

Use this end-to-end control flow:

```text
human-owned mathematical intent
              ↓
AI proposes the next Litex block
              ↓
Litex checks the candidate
   ├─ Committed → accepted context grows → propose the next block
   └─ RolledBack → accepted context is unchanged
                         ↓
                structured JSON evidence
                         ↓
                repair the same block ─────↗

contiguous committed prefix → materialized .lit → clean Litex gate
```

Apply these state rules:

1. The AI never self-accepts a candidate. Fluent mathematics, a plausible proof, or transport-level `ok: true` is not a committed declaration.
2. Read the exact nested transaction state. A `Committed` block may extend the live context; a `RolledBack` block must leave the accepted context unchanged.
3. Reader-facing labels such as `Accepted` and `Stopped` may summarize the branches, but journals must retain the real machine state and decisive verifier evidence.
4. On rollback, repair the earliest failed phase or goal in the same block. Do not advance as if the rejected fact were available.
5. JSON is the feedback interface and recoverable process memory. It explains why the next proposal changed; it does not become proof merely by recording a candidate.
6. Materialize only a contiguous committed prefix, then recheck it from a clean file-backed state before claiming file or module completion.

### Optional supported Lean handoff

Do not make Lean compilation a default success claim for every Litex development. Use this stage only when the user requests it, the relevant Litex evidence route is supported, the trust policy permits the handoff, and real Lean artifacts and gates are in scope:

```text
main.lit
   ↓
Generated.lean
   ↓
Adapter.lean
   ↓
Final.lean
   ↓
Lean kernel
```

The generated layer carries supported Litex evidence. The handwritten adapter is the only bridge the final native theorem may use to reach that generated layer; the public `Final.lean` statement should use ordinary Lean/Mathlib concepts. Claim `Lean-checked` only after the actual generated, adapter, and final artifacts pass the real Lean kernel gate. If the compiler does not support a proof route, or those artifacts were not produced and checked, stop the report at the Litex boundary and say so explicitly.

## The human–AI collaboration contract

### What the user supplies

At the beginning of a loop, help the user provide as much of this contract as the task requires:

```yaml
goal: the definition, theorem, chapter, or theory to construct
source: the mathematical source or intended formulation, if any
must_preserve: names, meanings, statements, assumptions, and source order
available_context: existing Litex files, interfaces, and earlier results
acceptance_scope: one block, one file, a module, or a larger development
trust_policy: whether assumptions or temporary trust are allowed
non_goals: nearby mathematics or implementation work outside the task
```

Do not force the user to decide routine syntax, local variable names, or a verifier-neutral proof bridge. Ask for a user decision only when alternatives change mathematical meaning, public interfaces, trust, architecture, source fidelity, or acceptance scope.

### What the AI returns before proof search

Before writing substantial Litex, return a compact decision briefing:

- the normalized mathematical goal;
- facts versus assumptions versus unresolved choices;
- the shortest natural-language proof or construction spine;
- the dependency graph of definitions, interfaces, and theorems;
- the first source-order block to attempt;
- the proposed journal, source, and verification boundaries; and
- any semantic decision that still belongs to the user.

The user should be able to correct the mathematics before verifier-oriented work begins.

### What the AI communicates during the loop

Keep the user informed at meaningful checkpoints, not after every mechanical command. Report:

- which mathematical block is active and why it is next;
- whether it committed or rolled back;
- the first decisive verifier phase or goal when it failed;
- the smallest evidence-backed repair being attempted;
- changes to statements, dependencies, trust, or public interfaces; and
- when a coherent accepted prefix has been materialized and replayed.

Continue autonomously through syntax fixes and semantic-neutral local repairs. Pause for the user when the next step requires a new mathematical assumption, a changed definition or theorem, a public API choice, a wider trust boundary, or materially broader scope.

## Derive the mathematics before writing Litex

Do not work backward from the desired final theorem by inventing convenient definitions or helpers. Derive the development forward:

```text
source mathematics and user intent
        -> exact concepts, carriers, and assumptions
        -> dependency graph of definitions and theorems
        -> shortest natural-language proof spine
        -> source-ordered Litex blocks
        -> verifier-backed accepted prefix
        -> final mathematical development
```

Apply these modeling rules:

1. Identify the mathematical objects and judgments before choosing Litex syntax.
2. Preserve standard mathematical meaning, source names, domains, codomains, quantifiers, and assumptions unless the user approves a change.
3. Search the existing project and Litex library for the highest established interface that performs each mathematical move.
4. Give every proposed definition or theorem an independent mathematical purpose. Do not create a wrapper or helper solely because the final target is currently difficult.
5. Keep proof-only machinery local. Promote it only when it is source-facing or has independent downstream consumers.
6. Make every nontrivial Litex block correspond either to one proof-spine move or to the smallest verifier bridge demonstrated necessary by a failed shorter attempt.

For a large theory, build a thin end-to-end mathematical spine first. Isolate substantial supporting obligations behind honest named interfaces, keep their status visible, and refine them without losing the main dependency structure.

## Transactional authoring loop

For a registered Litex target in this repository, build the current release binary once and start one persistent file-backed session:

```sh
cargo build --release
target/release/litex -session -f <current-file.lit>
```

For another installation, use its configured release Litex binary with the equivalent arguments. Do not silently substitute a debug or stale binary when the declared environment requires current release source.

Then repeat this loop:

1. Select the first not-yet-accepted source-order block.
2. Freeze its mathematical statement and exact dependencies.
3. Submit one definition, theorem, or small related fragment inside one literal outermost `try:` block.
4. Parse the nested transaction result. Transport-level `ok: true` only means that the request was handled; require `TryStmt.execution.kind = Committed` before treating the block as accepted.
5. Record the candidate and result in the JSON journal before changing it.
6. If the transaction rolled back, classify the earliest failing phase and make the next smallest correction in the same session.
7. If it committed, record `accepted_litex` without the outer `try:` wrapper and proceed to the next source-order block.
8. At a coherent theorem or file checkpoint, materialize the contiguous accepted prefix into the canonical `.lit` file.
9. Run a clean file-backed gate. If it fails, preserve JSON as the recoverable source of truth and return to the block loop.

Restart the session only when it exits or becomes unusable, the registered prefix deliberately changes, or an already committed declaration must be replaced under the same name. After a restart, replay the target from its first source-order block or from a verified materialized checkpoint as required by the environment.

## Failure triage

Classify the first decisive failure before changing the mathematical route:

| Phase | First response |
|---|---|
| Parsing | Reduce to the smallest syntax boundary and compare with current documented syntax. |
| Name or type resolution | Inspect namespace, source order, carriers, binders, and the exact registered interface. |
| Well-definedness | Expose the smallest missing domain, membership, nonzero, or construction requirement. |
| Proof verification | Compare the failed goal with the proof spine and add only the next mathematical fact or verified bridge. |
| Fact storage or environment mutation | Use a minimal control to distinguish a storage/runtime problem from a proof problem. |
| Later use or replay | Compare the committed session state with the clean materialized context and inspect qualification, ordering, and saved facts. |

Do not classify a kernel problem from one difficult proof. First compare the failure with the nearest direct control that preserves the suspected carrier, binder, operation, or proof action. Record both outcomes. Use `kernel_problem` only when the evidence isolates verifier or runtime behavior; otherwise preserve the intended mathematics and classify the remaining debt as `trust`.

## JSON proof journal

The journal is the recoverable working state shared by the user and the AI. It records concise decision evidence, not hidden chain-of-thought and not a raw terminal transcript.

Schema details may evolve, but preserve this semantic core:

```json
{
  "schema_version": 1,
  "target": "<registered Litex file>",
  "mathematical_contract": {
    "goal": "<intended mathematics>",
    "must_preserve": ["<semantic invariants>"],
    "acceptance_scope": "<block, file, or module>",
    "trust_policy": "<allowed boundary>"
  },
  "proof_spine": [
    "<first mathematical move>",
    "<next mathematical move>"
  ],
  "blocks": [
    {
      "id": "B001",
      "source_order": 1,
      "intent": "<one mathematical responsibility>",
      "dependencies": ["<accepted interfaces only>"],
      "attempts": [
        {
          "attempt_id": "B001-A1",
          "candidate": "<exact submitted Litex>",
          "transport_ok": true,
          "execution_kind": "RolledBack",
          "failed_phase": "<earliest failing phase>",
          "failed_goal": "<first decisive goal>",
          "verifier_evidence": "<concise exact evidence>",
          "diagnosis": "<evidence-backed interpretation>",
          "next_change": "<smallest falsifiable repair>"
        }
      ],
      "accepted_litex": "<committed source without try wrapper>",
      "status": "accepted_not_materialized"
    }
  ],
  "materialization": {
    "accepted_through": "<last contiguous block>",
    "clean_file_gate": "<command and parsed result>"
  }
}
```

Journal rules:

- Record every materially distinct candidate. Compress retries only when candidate, failure, and diagnosis are unchanged.
- Separate observation from interpretation: `verifier_evidence` says what Litex reported; `diagnosis` says what the AI infers from it.
- Make `next_change` small enough that the next verifier result can confirm or reject one hypothesis.
- Populate `accepted_litex` only after a committed transaction.
- Keep JSON as the staging source of truth during the inner loop; do not edit canonical `.lit` source after every speculative attempt.
- Record materialization, clean replay, trust scans, and broader gates separately from interactive success.
- To resume work, read the mathematical contract, proof spine, last materialized block, and first unaccepted block before proposing new code.

## Materialization and verification

At a coherent checkpoint, write only the contiguous committed prefix to the target `.lit` file in source order and without outer `try:` wrappers. Then run the smallest gate that establishes the declared acceptance scope.

For a registered file:

```sh
target/release/litex -f <current-file.lit>
```

Require both process exit code `0` and top-level JSON `ok: true`. Use a complete-module `-r` gate only when the user requested or accepted module-wide completion. Do not infer success from transport status, streaming output, or selected nested trace text.

After the clean gate:

1. audit every active `trust`, `abstract_prop`, axiom, assumed object, and unverified import;
2. confirm that the theorem statements, definitions, source order, and public interfaces still match the mathematical contract;
3. confirm that JSON `accepted_litex` and the materialized prefix agree; and
4. report exactly what was checked and what remains outside the checker claim.

## Proof quality after acceptance

Once a proof verifies, align it with the natural-language proof spine:

- remove facts that have no live mathematical consumer;
- remove result echoes, wrapper echoes, duplicate endpoints, and bypassable chains;
- keep explicit reader bridges when they reveal a real conceptual transition;
- keep verifier bridges only when a deletion probe in the real context shows they are necessary;
- avoid top-level helpers that serve only one proof; and
- reuse stable mathematical interfaces instead of reconstructing their implementations.

Test each meaningful deletion transactionally. If the shorter form fails, restore only the smallest bridge supported by the failure evidence. The final `.lit` file should communicate the mathematics, not replay the verifier's internal state history.

## Unresolved obligations and trust

Do not let one hard subgoal stall an otherwise useful dependency chain indefinitely. Use the project's explicit proof-search budget. When no budget is supplied, use the repository default: at most three active minutes for the first direct attempt, then the narrowest marked `trust` on only the blocked substep so the mainline can continue. After the chain runs, revisit each trust for at most five active minutes. Do not begin a third search round without user approval.

For every surviving obligation:

- preserve the intended mathematical statement;
- keep trust as narrow as possible;
- record both search rounds and the exact missing fact or capability;
- classify it as `trust` or `kernel_problem`;
- state the acceptance command that would discharge it; and
- never report the affected theorem as `checkable`.

Use these result states consistently:

- `translated`: the intended mathematics has a natural Litex formulation;
- `checkable`: the relevant materialized development passes its declared gates with no unresolved trust; and
- `blocked`: the intended statement is preserved and the concrete boundary is recorded.

## User-facing checkpoints and handoff

At each coherent checkpoint, give the user a compact state report:

```text
Mathematical goal: <unchanged or explicit approved change>
Accepted prefix: <last committed/materialized block>
Current block: <mathematical responsibility>
Verifier state: <committed or earliest rollback phase/goal>
Evidence: <journal path and attempt id>
Next action: <smallest repair or next dependency>
User decision needed: <none or exact semantic choice>
Trust boundary: <current assumptions and debt>
```

At completion, lead with the mathematical result, then provide:

- the canonical `.lit` artifact;
- the JSON journal or journals;
- the exact file and module gates that were run;
- their process exit codes and top-level results;
- the remaining trust and checker boundaries; and
- the next smallest action if any scoped work remains.

The user should be able to understand what mathematics was constructed, inspect why the AI made each decisive repair, resume from the last accepted prefix, and distinguish verified results from proposals or assumptions.
