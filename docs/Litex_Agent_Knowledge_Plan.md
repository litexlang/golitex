# A Litex Reference System for Agents and Contributors

Design plan, 2026-10-07.

Build a small task-oriented entry into Litex's existing documentation and
mathematical examples. A new agent or contributor should be able to find an
appropriate interface, understand its conditions, run a proof, interpret the
feedback, and explain what the result establishes.

Litex's useful organizing principle is the growth of checked context: one
statement introduces objects or establishes facts that later statements can
consume. A reference system should teach that progression through real code,
including domains, scope, explicit proof steps, and assumptions. Its success
must be measured on new tasks, rather than by the number of indexed files.

This document specifies the reference system and its rollout. The initial
[Agent Guide](AgentGuide.md) now teaches persistent Session context, failure
interpretation and current-version verification, with a checked artificial
example. The catalogue, generated navigation and agent evaluation remain
future work; this guide does not complete those rollout phases.

## One task through the proposed system

Suppose a reader asks: "Define the reciprocal on nonzero reals and prove that
multiplying it by its argument gives one."

The [Manual's R01 recipe](Manual.md#r01-define-and-use-a-reciprocal-function)
already contains the proof:

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
claim:
    ? forall x R:
        x != 0
        =>:
            reciprocal(x) * x = 1
    reciprocal(x) = 1 / x
    reciprocal(x) * x = (1 / x) * x = 1
```

The guard makes the body meaningful throughout its declared domain. In the
claim, the defining equation exposes the value needed by the product equality.
The successful claim exports its universal conclusion; its binder remains
local to the proof.

The nearest domain boundary is documented in
[P02](Manual.md#p02-the-body-must-be-meaningful-throughout-the-function-domain):

**Expected rejection, not a positive tutorial:**

<!-- litex:skip-test -->
```litex
have fn reciprocal(x R) R = 1 / x
```

This signature includes zero. Checking the anonymous function body fails at
`have_fn_equal`. If the intended function is the partial reciprocal, use its
nonzero domain. A function defined at zero needs a different mathematical
definition, specifying that value.

Currently, the reader must discover these connections across the Manual and
examples. The proposed lookup returns one small reference packet:

1. The task's mathematical meaning and domain.
2. [S01](Manual.md#s01-expression-defined-functions) for the callable definition.
3. [O01](Manual.md#o01-division) for division conditions.
4. R01's complete proof and
   [P05](Manual.md#p05-a-function-equation-may-need-to-be-exposed-before-substitution)
   for the explicit equation step.
5. P02's rejection and a verification receipt for the selected source.

The Litex code stays the same. The change is that a task leads directly to its
relevant contracts, proof route, and boundary. This example establishes a
reference shape; it does not establish that arbitrary identities are found
automatically.

## Existing sources and their responsibilities

Keep each source responsible for its current subject. The new entry should
route readers into these sources and cite exact sections or examples.

| Source | What it supplies |
| --- | --- |
| [Learner Cheatsheet](Litex_Learner_Cheatsheet.md) | First contact, object/fact/statement distinctions, and ordinary authoring choices. |
| [Manual](Manual.md) | The canonical language and proof contracts, S/O/F/C entries, pitfalls, mathematical recipes, and the system/component map. |
| [CLI](cli.md) and [setup](setup.md) | Installation, supported commands, project mounting, output, and process status. |
| [Examples](../examples/README.md) | Small statement, proof, inference, and well-definedness tracers. |
| [Statement fixtures](../examples/test_statements/README.md) and their [manifest](../examples/test_statements/manifest.json) | Existing executable expectations, including rejection and rollback cases. |
| [Math showcases](../showcases/math_concepts_in_litex/README.md) | Complete, bounded mathematical developments and concrete consumers of their interfaces. |
| Published textbook material | Longer learning sequences, chapter dependencies, and proof development in source order. |
| Module-owned `README.md` and `math_collections.md` | Implemented interfaces, mathematical design, dependencies, use examples, and known boundaries. |
| Owner-specific `src/` and `tests/` | Implementation and regression evidence for contributors changing the verifier. |

[Reference.md](Reference.md) is a relocation notice; its entries now belong to
the Manual. Do not create a second maintained language dictionary.

Treat historical audits as dated evidence. A past passing record must retain
its source and verifier identity; it does not automatically certify today's
source. Internal fixtures and exploratory material should keep their declared
role when referenced.

## Proposed deliverables

The initial guide and its AGENTS entry exist; the remaining paths and expansion are proposed.

| Artifact | Responsibility |
| --- | --- |
| [`docs/AgentGuide.md`](AgentGuide.md) | Implemented initial entry: context growth, persistent Session repair, current verification and focused reference routing. |
| `docs/knowledge/index.json` | One maintained catalogue of task meanings, references, conditions, roles, and validation receipts. |
| `docs/knowledge/README.md` | Browsable navigation generated from the catalogue. |
| Entry from root `AGENTS.md` | Implemented; retains repository working agreements and foregrounds the Session workflow. |

Human readers may follow the learner-to-example-to-showcase-to-textbook path.
Agents may select a task and load only its reference packet. Both paths use
the same underlying contracts and examples.

Start with stable identifiers, tags, and ordinary text search. Use English
and Chinese search phrases for common mathematical intentions. Markdown and
JSON keep the material usable without a particular agent platform. Any future
platform skill should be a thin entry into this maintained source.

## Catalogue entries and evidence

Index mathematical intentions and authoring actions: define a callable value,
prove a set equality, obtain a witness, prove uniqueness, use induction, expose
a defining equation, or establish a divisor condition. Include subject tags
such as arithmetic, sets, functions, and geometry. Preserve the existing
phase-oriented example paths for implementation work.

Each entry needs:

- A stable id, task description, keywords, and mathematical/proof-action tags.
- Canonical references with section anchors or an exact example/case selector.
- Required declarations, assumptions, imports, and configured source order.
- The useful fact or interface that successful code makes available next.
- A material role and expected behavior: positive tutorial, regression,
  expected rejection, or draft.
- The nearest relevant boundary and its executable expectation when available.
- A validation state and receipt; unknown evidence stays explicitly pending.
- A reviewed assumption boundary, including relevant imported assumptions.

For example, a seed entry could have this shape. It is an illustrative schema;
the pending fields are not verification claims:

```json
{
  "schema_version": 1,
  "id": "guarded-reciprocal-law",
  "intent": "Define a reciprocal and prove its product law",
  "keywords": ["reciprocal", "division", "倒数", "分母非零"],
  "role": "tutorial",
  "source": {
    "path": "docs/Manual.md",
    "anchor": "r01-define-and-use-a-reciprocal-function"
  },
  "conditions": ["The argument is real and nonzero"],
  "provides": ["The guarded callable interface and universal product law"],
  "boundary": {
    "path": "docs/Manual.md",
    "anchor": "p02-the-body-must-be-meaningful-throughout-the-function-domain",
    "expected_outcome": "reject",
    "expected_phase": "have_fn_equal"
  },
  "validation": {"state": "pending"},
  "assumptions": {"review": "pending"}
}
```

The implemented schema must distinguish material role, verification result,
and assumptions. A negative case can pass its rejection test while remaining
unsuitable as a successful proof. An ordinary run containing `trust` can
succeed while retaining proof debt. An `abstract_prop` declaration introduces
a signature; it does not prove instances.

Receipts should identify the exact selected code, configuration and loaded
dependencies, source revision or snapshot, verifier build identity, command,
date, exit status, and parsed outcome. Reject stale receipts when those inputs
change. Absence of direct `trust` is insufficient evidence about dependencies;
strict acceptance also retains the verifier's builtin and foundation boundary.

Collect paths, source fingerprints, and run results automatically. Curate task
meaning, representative examples, and scope deliberately. Reuse existing
fixture manifests and receipts rather than maintaining conflicting expected
outcomes. Keep case/fence selectors precise so an executable test selects the
intended block, not a neighboring example.

## The authoring and repair workflow

The entry should teach this sequence:

```text
understand the mathematics and intended statement
  -> inspect existing builtin, stdlib, and module interfaces
  -> retrieve a small relevant reference packet
  -> check domains, assumptions, imports, and scope
  -> submit a small source fragment
  -> inspect feedback and committed context
  -> repair the current stopping point
  -> independently verify the complete final artifact
  -> retain the proof and any unresolved debt
```

For the reciprocal task, the packet supports a specific decision: inspect the
nonzero domain when body WD fails; inspect the defining equation when a larger
product does not verify. A search miss does not prove a negation. It also does
not, by itself, establish a kernel bug.

Describe supported syntax, recommended style, and required conditions
separately. For example, `release thm` is the recommended unselected theorem
call; a selected atomic consequence still uses `by thm ... => fact`. Preserve
the intended mathematics during repair instead of changing its domain or
adding an unsupported premise merely to obtain success.

Run recipes must follow the checked-out version's [CLI contract](cli.md).
The current standalone batch check is:

```bash
target/release/litex -lang en -strict -f example.lit
```

Build current source with `cargo build --release` when validating a development
checkout. A configured file can require earlier exports and imported modules;
record that context rather than treating every file as standalone. Use the
current REPL/session protocol for interactive work, and a separate batch run
for the final machine-readable check.

For a positive batch, require exit code 0 and a parsed envelope with
`kind == "run"`, `success == true`, and `session_error == null`. Expected
negative cases must match their specific verifier/parser boundary; crashes,
timeouts, malformed output, and invalid CLI arguments are test failures.
Older `-compact`, `-runner`, `-before`, or `ok` recipes must not be copied into
this version's entry. The guide should point to CLI rather than duplicate its
full output specification.

## Ownership and maintenance

The author changing an interface or capability should update its applicable
Manual entry, representative example, boundary expectation, and catalogue
entry in the same change. Generated navigation must be reproducible from the
catalogue. Collection and validation tooling intended for this repository can
live under the existing `tests/tooling/` area.

Changes to source, project configuration, dependencies, or the verifier mark
affected receipts stale. Revalidate the affected entries using focused gates.
When verifier impact is uncertain, retain the historical receipt and label
current compatibility unknown until the relevant checks establish it.

Local textbook authoring follows the workspace registry `scripts/.textbooks`
and its canonical module ownership. The entire root `scripts/` workspace is
local-only. Public navigation should use an actually published module or
repository with an identifiable version and accessible dependencies. It must
not copy, expose, or automatically publish local textbook workspaces. Check a
public entry from a clean checkout before advertising it as runnable.

Record new failures in the owning task/source evidence and todo. Promote a
repair into permanent agent guidance only after independent examples and
boundary checks support a reusable rule. A single failed task or successful
workaround is insufficient evidence for a language-wide instruction.

## Rollout and acceptance

| Phase | Deliverable | Acceptance |
| --- | --- | --- |
| 1. Curated entry | Short guide and 20–30 high-frequency task entries covering definitions, arithmetic/order, sets/functions, witnesses/uniqueness, induction, and contradiction. | Every entry has a precise accessible source, conditions, expected behavior, boundary, and current validation or an explicit pending state. |
| 2. Validation and navigation | Generated browsing index, link/context checks, and receipt generation reusing existing test expectations. | Navigation is reproducible; changed inputs invalidate evidence; negative cases require their actual rejection. |
| 3. Agent evaluation | A fixed set of new tasks excluded from catalogue curation, plus a recorded baseline. | Compare task success, incorrect commands, validation rounds, time/context cost, assumption reporting, and boundary failures. |
| 4. Expansion | More subjects, modules, and accessible textbook references, selected from actual use. | Extend coverage while preserving the same ownership, version, and validation contracts. |

Use roughly ten held-out tasks for the first evaluation. Include proof
construction, definition choice, failure diagnosis, and module reuse. Give the
agent only the normal repository entry and its stated tool budget; record the
agent version, instructions, and available files. Human contributors should
also be able to follow the generated navigation.

Before running the evaluation, fix the baseline, task meanings, budgets, and
success criteria. Count a solved task only when the intended final statement
passes its independent gate and its assumption boundary is accurately
reported. Report unfinished and blocked tasks without relabeling them as
completed proofs. No agent improvement or corpus-wide verification is claimed
by this plan.

## Verification of this document

The document's reciprocal proof and its expected domain rejection were checked
independently on 2026-10-07 after `cargo build --release`, using the exact fenced
source with `target/release/litex -lang en -strict -f <extracted-block.lit>`.
The verifier reported `Litex 1.0.0-beta`, built from repository revision
`49112c27ff45731dbdbde7b6ceef833376bfdb83`; the new document was uncommitted.
The verifier binary SHA-256 was
`b2b4da58c1d3490af948fcb66862b16a100001b1a6b2e07f432aa3105d5adb61`.

| Check | Observed result |
| --- | --- |
| Reciprocal proof | Exit 0; `kind: run`, `success: true`, `session_error: null`. |
| Missing nonzero domain | Exit 1; `success: false`, `session_error: null`, failed phase `have_fn_equal`. |
| Existing local links and section anchors | All 15 references resolve. |
| Illustrative catalogue JSON | Parses successfully; pending fields remain explicitly illustrative. |

These focused checks concern the representative code and document references
only. Implementing the catalogue, evaluating agents, and validating the
remaining corpus are separate future acceptance steps.

The initial Agent Guide's persistent-session example has separate
[verification evidence](../tests/tooling/acceptance/agent-session-guide-2026-10-07.json).
It checks context retention and failure boundaries, not the proposed catalogue
or agent evaluation. That receipt identifies its isolated HEAD release build
and the unrelated working-tree compilation limitation.
