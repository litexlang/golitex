---
name: todo_writer
description: Write or update Litex todo artifacts in the applicable source or translation workspace, including todo.md blocker lists, unfinished notes, and solved-experience records. Use when Codex records textbook trust or abstract_prop holes; unfinished mathematics; failed formalization attempts; strange verifier/parser behavior; missing examples; or local translation workspace todo items.
---

# Todo Writer

## Critical: Repository Policy And Verifier Loop

When a todo diagnosis executes Litex rather than only editing comments:

- In the golitex repository, apply `$golitex-repository-policy` alongside this
  skill and read its canonical bundled policy completely. That repository
  policy overrides generic or older guidance here.
- Build current source once with `cargo build --release` and invoke
  `target/release/litex`; never use `target/debug/litex`.
- For every iterative reproduction in a registered target, start one
  `target/release/litex -compact -session -before <current-file.lit>` process.
  Submit target statements from the first one in source order, one literal
  outermost `try:` block per reproduction or small candidate fix. Write each
  accepted statement back without the wrapper; retry only the current failed
  block in the same process.
- Once a real blocker is identified, keep the intended statement, use the
  narrowest legal `trust`, record the concrete debt, and continue. Do not spend
  further proof-search iterations unless the user asks to remove that trust.
- Restart only when the process exits or cannot accept another frame, the
  registered prefix deliberately changes, or an already committed declaration
  must be replaced under the same name. Replay the target from its first
  statement after a restart. Record an unexpected unusable session as
  `kernel_problem`.
- Use `target/release/litex -compact -f <current-file.lit>` for a clean
  baseline, checkpoint, or final file gate. Use `-isolated -f` only for an
  intentionally standalone reproduction.
- Optionally use
  `target/release/litex -compact -f <current-file.lit> -trust-before-line <X>`
  as a disk-first suffix preview or fallback, never as the default loop. `X`
  must be the exact physical header line of the first changed or
  not-cleanly-verified top-level statement; move it backward after any earlier
  edit. The prefix is parsed and registered but skips well-definedness and
  proof verification, so dependent suffix results are `indirect_trust` and the
  run is not `checkable`. It is incompatible with `-session`, `-r`, and
  `-strict`; always finish with a clean `-f`.
- Reserve `target/release/litex -compact -r <module>` for an explicit complete
  module or repository gate. Never use default-profile `cargo test` as the
  Litex verifier; run the smallest genuinely required
  `cargo test --release ...` harness separately.

Use this skill when writing or updating todo/blocker notes for Litex work.
The output is for the project owner to act on, not a generic status summary.

## Textbook Todo Boundaries

Keep textbook todos, audits, translation-item records, unfinished notes,
experience notes, verifier captures, and generated Markdown in the book's
paired source workspace, such as `scripts/Analysis/`. For Analysis I, keep
chapter tracking under `scripts/Analysis/todo/`.

Do not create todo artifacts inside either textbook module tree:

- `scripts/textbooks_drafts/<Book>/` is the canonical editable module and
  contains only artifacts intended to ship with the book, including its one
  `README.md` and `math_collections.md`.
- `textbooks/<Book>/` is the read-only published snapshot unless the user
  explicitly requests publication.

Record mathematical holes and technical blockers in the nearby workspace
`todo.md` or unfinished-note convention. Locate a mathematical hole by chapter,
section, and named source item; state the exact missing mathematics and what is
already established. Include engineering evidence in the same workspace item
when it affects the diagnosis.

## Core Rule

Every todo item must include a concrete example. No example means no item.
Do not write a broad library wish unless you show the code, source item, or
verifier behavior that forced that conclusion.

Every file written under `todo/` or another todo-like folder must also record
its task provenance near the top. A development todo without an associated
task is incomplete.
Use a compact block such as:

```markdown
## Task context

- Task: <the user request or stable task title>
- Scope: <the files/source/workflow covered by this todo>
- Related workspace: <repository or source workspace>
```

When updating an existing todo, preserve its task context and extend it if the
scope changes. Do not infer a vague task title from the filename alone; use the
user request, issue, milestone, or explicitly named workflow that caused the
todo to be created.

A good item answers:

1. Where did this happen? Give file path, source id, theorem name, or dataset item.
2. What was attempted? Include the relevant Litex snippet or statement shape.
3. What failed or was unclear? Include exact verifier output if available.
4. What would unblock it? Give the desired theorem/interface/syntax/diagnostic.
5. Which primary blocker label applies? Use exactly `trust` or
   `kernel_problem`.

## Completed Items

For development todo items, if an interaction with the user resolves an item,
do both steps before calling the work complete:

1. Record how it was solved in the matching local finished/experience area.
   Use the source workspace's convention when it exists, such as
   `experience/problem_notes/` or `finished/`. If no convention exists, create a
   nearby `experience/problem_notes/` folder next to the todo file.
2. Remove the completed item from the todo file.

The finished note should include the original blocker, the concrete Litex or
code pattern that solved it, any verifier command used, and the reusable lesson.
Do not only delete the todo item; preserve the solution path first.

## Cross-Turn Project Ledgers

For an unfinished Litex textbook, proof, kernel, stdlib, or documentation task
that spans turns, create or update a repository-root ledger at
`todo/<YYYY-M-D>/<project>.md`, using the current environment date without
zero padding. This is a workflow ledger, not a source-local blocker list.

Start it before substantial work. Keep it compact:

```markdown
# Project title

## Task context

- Task: <the user request or stable task title>
- Scope: <the files/source/workflow covered by this ledger>
- Related workspace: <repository or source workspace>

Status: in progress

## Completed
- Concrete change or audit result, with file path and command evidence.

## Remaining
- [ ] Exact next action, affected files, and expected verification command.
```

Update it at each meaningful checkpoint. Preserve ordinary source-local
experience notes for resolved mathematical blockers; when the entire scoped
project task is complete and verified, delete the dated project ledger.

For source-local `todo.md` files, add the same `Task context` block near the
top, naming the parent translation/proof task and the source slice. For
experience or finished notes created under a todo-related folder, retain the
task title and scope in a short front-matter or opening section so the solution
can be traced back to the original task.

## Blocker Labels

Every blocked item has exactly one primary label:

- `trust`: the proof or formulation is incomplete, including missing
  definitions, lemmas, theorem organization, automation, syntax, diagnostics,
  or other non-kernel work.
- `kernel_problem`: evidence points to verifier, runtime, well-definedness,
  proof-model, or other kernel-level behavior.

Describe the likely cause and next action in ordinary prose. Do not introduce
additional coded blocker categories.

## Item Format

Prefer this compact structure:

````markdown
## trust

### path/or/source-id: short problem title
- Example attempted:
  ```litex
  forall x, y R:
      x >= 0
      y >= 0
      =>:
          sqrt(x * y) <= (x + y) / 2
  ```
- What happened: verifier could not justify the inequality step; include exact
  output if available.
- Why this matters: needed for the AM-GM item in `required-1.lit`.
- Desired interface: a checked theorem such as `Real::am_gm_two_nonnegative`.
- Primary blocker: `trust`.

## kernel_problem

### path/or/source-id: short surprising behavior
- Example attempted:
  ```litex
  ...minimal repro...
  ```
- What happened: exact parser/verifier/CLI behavior.
- Expected behavior: what a reasonable Litex proof writer expected.
- Follow-up: likely syntax, diagnostics, infer-rule, kernel, or docs work.
- Primary blocker: `kernel_problem`.
````

## Writing Standards

- Keep one todo item per concrete blocker. Split unrelated missing theorem
  packages into separate items when they have different examples.
- Prefer source-local names over broad topics: `required-1.lit: AM-GM` is better
  than `Inequalities`.
- Avoid phrases like "full theorem package is missing" unless followed by the
  exact theorem statement or proof step that failed.
- Avoid saying only "need geometry theorem interfaces". Show the conic, angle,
  line-circle, or circle-circle statement that could not be checked.
- If no Litex code was attempted, say that explicitly and include the
  natural-language statement that still needs a Litex formulation.
- If exact verifier output is unavailable, say `Exact output not captured` and
  include the command or file that should be rerun.
- Before recording `trust`, try one direct formulation in the real caller
  context and capture the exact result. Once that result identifies a real
  blocker, use the narrowest legal source `trust` immediately and record it;
  do not continue proof search unless the user asks to remove the trust.
- Remove completed items only after recording the solution in the matching
  finished/experience file.

## Bad To Good

Bad:

```markdown
- `trust`: Full finite-sum formulas for arithmetic and geometric
  sequences are not packaged.
```

Good:

````markdown
### optional-1.lit: finite geometric-series sum
- Example attempted:
  ```litex
  forall a, r R, n N:
      r != 1
      =>:
          sum(0, n, '(k Z) R {a * r^k}) = a * (r^(n + 1) - 1) / (r - 1)
  ```
- What happened: direct equality proof could not be verified from current sum
  rules; exact output not captured.
- Why this matters: optional sequence item needs closed forms for geometric sums.
- Desired interface: a checked finite geometric-series theorem with domain facts
  for `r != 1` and natural upper bounds.
- Primary blocker: `trust`.
````
