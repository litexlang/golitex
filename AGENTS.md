# Litex Local Instructions

Always apply these rules when working in this repository.

## Project Direction Through September

The main project direction through September is to use real mathematical
translation work as a pressure test for Litex. The target sources include
Mathematics in Lean, Terry Tao's Analysis I, miniF2F, MATH500, high-school
mathematics datasets, and Weil's Number Theory for Beginners.

The purpose is twofold:

1. Build strong evidence that Litex can express and verify meaningful
   mathematics quickly.

2. Use translation failures to discover real language, standard library,
   kernel, inference, automation, and diagnostic gaps.

Treat this as a structured feedback loop, not as a line-by-line porting
project. For each source, start with a small vertical slice before attempting
large-scale coverage. A useful slice is around 20-50 representative problems,
definitions, or theorem statements.

For each translated item, follow this loop:

1. Understand the mathematics first.

2. Write a natural Litex statement and proof attempt that matches the current
   verifier style.

3. Run the verifier and read the exact output.

4. Make the next smallest correction.

5. Classify the result as one of:
   - `translated`: the mathematical statement is naturally expressed in Litex.
   - `checkable`: the statement and proof are fully verified by Litex.
   - `blocked`: the failure reason is understood and recorded with a minimal
     reproduction.

Classify blockers explicitly with only these labels:

1. `proof_debt`: the current proof is not complete. Use this for missing
   definitions, lemmas, theorem organization, automation, syntax, diagnostics,
   formulation work, or any case where the honest statement is that we do not
   yet know how to finish the proof in Litex.

2. `kernel_problem`: the issue appears to be in Litex's verifier, runtime,
   well-definedness logic, core proof model, or another kernel-level behavior
   rather than in the current proof attempt.

Prefer early work on low-dependency, high-feedback corpora such as MATH500,
high-school math, and small miniF2F slices. Use Mathematics in Lean as a
standard library roadmap. Use Tao's Analysis I and Weil's Number Theory for
Beginners as deeper stress tests for structured definitions, chapter
dependencies, and long-form mathematical development.

Successful translations should become examples, benchmarks, or documentation
snippets when appropriate. Failed translations should become minimal blockers
that guide standard library work, language design, kernel improvements, or
better diagnostics. It is acceptable to use `know` or `abstract_prop` only when
the blocked part is clearly labeled and the rest of the development remains
explicit and checkable.

When a textbook theorem overlaps with Litex builtin behavior, kernel support,
or a broad standard-library theorem, keep both roles visible. Preserve the
source theorem as a local textbook-facing statement so chapter coverage and
dependencies remain traceable. Use the Litex/std theorem as the main proof
source when it exists or is the intended trusted interface. If the source proof
is pedagogically important but not yet the main checked path, place its proof
shape in a local `prove` block, proof sketch, or nearby todo as an alternate
route/proof debt rather than replacing the chapter statement.

For textbook chapter files, follow the source order when introducing local
definitions. Do not put a large block of chapter-wide `prop` or
`abstract_prop` declarations at the top unless the source itself starts that
way. If Litex already has a builtin concept or standard predicate such as
membership, subset, finite sets, `count`, tuples, Cartesian products, or
function equality, use it directly instead of adding a Tao-specific wrapper.
Record broad proof debt in nearby comments or todo files; only introduce a
named prop when it is a real source definition or a reusable local interface
that later checked statements actually depend on.

Use source-local cite packages for lengthy supporting facts. This is the
preferred workflow for textbook and dataset formalization when the main
mathematical line is clear but a surrounding fact has a long, routine, or
library-shaped proof. Keep the main chapter or problem file focused on the
source-facing definitions, theorem statements, core proof route, and checked
derivations. Put the surrounding fact into an adjacent module such as
`chap7_cite/main.lit`, `<source>_cite/main.lit`, or a local `cite/main.lit`.
The main file should import this module with `import "../chap7_cite"` or the
analogous relative module import; do not use `run_file` for cite packages.
Reserve `run_file` for source-order reuse such as one chapter loading an
earlier chapter.

Cite packages are explicit proof-debt interfaces, not completed standard
library modules. Facts in a cite package should be named `thm` or `claim`
interfaces whose unproved step is marked with `know`, and each such debt should
be tracked in the nearby `todo.md` or unfinished notes. An imported cite module
must be self-contained: import the std modules it needs, and put shared source
vocabulary in a small real `prop`/`have` module such as `chap9_vocab/main.lit`
rather than copying existing chapter definitions as `abstract_prop` inside the
cite package. Use `abstract_prop` only for genuinely external background
interfaces that do not yet have a usable definition. Only move a cite theorem
into `std` after its statement is stable, its proof or intended trusted
interface is understood, and multiple files genuinely need it.

By September, a good outcome is not only a large number of translated items. A
good outcome is a working translation pipeline, checkable examples across the
main source families, a clear standard library gap map, a benchmark set for
Litex's mathematical ability, and minimal reproductions for the important
blockers.

For every source folder under `scripts/` or a similar local translation
workspace, maintain a nearby `todo.md` as the local blocker list for that
source. When translation work reveals a missing definition, theorem, infer
rule, builtin rule, syntax feature, or diagnostic gap, append a concise item to
that folder's `todo.md`. When one of those items is implemented or no longer
blocks the work, remove it from that `todo.md`. For example, if work in
`scripts/minif2f_tmp/` hits a missing feature, record it in
`scripts/minif2f_tmp/todo.md`; if the feature is later added, delete the
completed item.

## Dataset And Textbook Problem-Solving Loop

Use this loop for MiniF2F, MATH500, high-school datasets, Mathematics in
Lean, Tao Analysis, Weil Number Theory, and any other dataset or textbook
translation work. The goal is a pressure-test workflow, not only a final
answer.

For every dataset, textbook, contest, exam, or generated-math item that is
newly created or touched, maintain a structured translation item record with
this shape:

```yaml
source:
problem:
proof_idea:
litex_code:
comments:
```

Use these fields consistently:

- `source`: dataset, book, exam, contest, or source name.
- `problem`: source problem, theorem, exercise, or a reusable reformulation if
  the source text cannot be redistributed.
- `proof_idea`: the mathematical idea before Litex code.
- `litex_code`: the current runnable or intended Litex code.
- `comments`: verifier command, proof attempt notes, blocker label, source or
  license caveats, and follow-up work.

Do not submit only raw Litex code for a translation item. Record the
mathematical idea and, in `comments` or local tracking, the current status. Do
not mark an item `checkable` unless the relevant Litex code has been run and
verified. If source text cannot be redistributed, record a reusable
mathematical reformulation and put the license concern in `comments`. Existing
datasets do not need to be migrated all at once, but newly created or modified
records should follow this contract.

If a workspace needs dashboard or batch-tracking fields such as `id`, `topic`,
`difficulty`, `status`, or `blocker`, add them locally, but do not treat them
as required fields for ordinary translation records.

For each item, proceed in this order:

1. First explain the natural-language mathematical idea. Work out the key
   transformations, cases, witnesses, estimates, or theorem dependencies before
   writing Litex.

2. Translate that mathematical plan into a natural Litex formulation. Prefer a
   proof shape that the current verifier can check: explicit equality chains,
   small intermediate facts, finite case splits, witnesses, named theorem
   calls, and local reusable lemmas.

3. For textbook work, if the source theorem can be proved by following the
   text but Litex also has builtin/kernel/stdlib support for the same fact,
   record both routes. Keep the source theorem statement in the chapter file,
   use the named Litex/std interface as the main checked route when available,
   and keep the textbook proof idea in a local `prove` block, proof sketch, or
   nearby todo until it is checkable.

4. If a supporting fact is lengthy, routine, or only needed as a background
   citation for the current source item, put it in a source-local cite package
   and import that package from the main file. This keeps the main file
   readable while preserving a named theorem interface and explicit proof debt.

5. If the proof cannot be completed immediately, write the best partial Litex
   proof first. It is acceptable to use `know` temporarily, but only for the
   blocked step. Next to each temporary `know`, add a concise comment saying
   why the step is not yet proved and what kind of missing support it appears
   to need.

6. Put unfinished attempts in the local unfinished-explanation area. In
   MiniF2F this is
   `scripts/litex-minif2f/unfinished_dataset/problem_notes/`.
   For another dataset or textbook workspace, create the analogous nearby
   folder if it does not already exist. Name the file by the problem or theorem
   id. Record the proof idea, the current Litex attempt, the exact verifier
   failure if any, every remaining `know`, and the primary blocker label.

7. Iterate by removing proof debt one step at a time. Run the verifier after
   each small change and use the exact output to decide the next correction.
   Try splitting algebraic or numeric jumps into smaller equalities before
   searching for new theorems.

8. When the item becomes checkable, move it out of the unfinished area and into
   the finished area for that source. Delete the matching unfinished-explanation
   file, update any local JSONL/status/todo bookkeeping, and keep the final
   `.lit` file runnable.

9. After solving a formerly unfinished item, write a short "war story" in the
   local solved-experience area. In MiniF2F this is
   `scripts/litex-minif2f/experience/problem_notes/`. For another
   source, create the analogous nearby folder if needed. Record the natural
   idea, where the attempt got stuck, the exact trick or Litex pattern that
   solved it, and any reusable lesson for later items.

When splitting backlog work, use disjoint ranges or families. Use read-only
triage passes to classify unfinished items, and use workers only on clearly
separated write scopes. Each worker should return the status for each item it
touched: `checkable`, `translated`, or `blocked` with one primary blocker
label.

## General Engineering Style

1. Read the nearby code before editing. Follow the existing data model, naming, and control flow unless the user asks for a redesign.

2. Write simple code, not clever code. Avoid fancy Rust syntax when a direct expression is clearer.

3. Keep changes scoped to the request. Do not rewrite unrelated code or clean up unrelated files.

4. Use English for comments and documentation. Comments should be concise and explain the purpose of non-obvious logic.

5. Do not add many comments. If the code is simple, make the code clear instead of adding comments.

6. Do not break existing data structures. Add adapters or helpers only when they preserve the current shape of the system.

## Rust Kernel And Codebase Rules

1. Use `use crate::prelude::*;` for repository imports. Import only `std` items directly.

2. Use `.into()` to convert between types instead of directly wrapping a struct with an enum variant such as `Enum::Variant(value)`.

3. Do not write code in `mod.rs`; `mod.rs` is only for module definitions.

4. Use a static `new` function to create a new instance of a struct instead of using the struct literal constructor directly.

5. Do not write static functions inside a struct when the struct is not needed. Use a free function instead.

6. Do not write too many functions. If a piece of code is simple and only called once, write it inside the function that calls it.

7. Write shared helper functions in a `helper.rs` file, not at the head of a file.

8. Do not write new helper functions at the beginning of a file. Put them near the end of the file. The beginning of a file should contain major functions or struct definitions.

9. When implementing a builtin rule, write comments about what mathematical property the rule is for, and include an example.

10. When implementing an infer rule, write comments about the condition under which the rule is applied and what new fact is inferred. Include an example.

11. All runtimes created within one top-level run must share the same module manager. In particular, imported-module runtimes should be created with `Runtime::new_for_import_from_parent` so nested imports, cycle checks, source labels, and stopped-module state all update the same `Rc<RefCell<ModuleManager>>`.

## Litex Language And Proof Style

1. Litex examples should expose a tight verifier feedback loop: write a small proof, run it, read the exact verifier output, and make the next smallest correction until the proof is checkable.

2. Before writing Litex code, first explain the proof idea in natural language and look for the local proof pattern. Prefer starting from the mathematical move that should work in Litex rather than searching for theorem names as if the task were Lean.

3. When several formulations are possible, prefer the most Litex-native and
   simplest checkable formulation. Do not preserve a source text's original
   shape, or Litex's lower-level raw expression shape, if doing so creates
   special cases or a harder proof. If preserving the source shape is important
   for comparison, record it separately and keep the main checked proof simple.

4. Do not rely on external mathematical libraries when writing Litex examples unless the user explicitly asks for that. Prefer proof steps that the current Litex verifier can check directly.

5. Make documentation and Mechanics of Litex Proof `litex` fenced blocks self-contained. A snippet should not depend on a previous snippet sharing the same environment. If a block is illustrative only, mark it with `<!-- litex:skip-test -->`.

6. Any time the user asks for code that makes some Litex code verifiable, write the Litex code in `examples/tmp.lit` and test it, so the user can run it directly.

7. When writing ordinary Litex `forall` facts, do not write an empty implication body. Write:

```litex
forall x R:
    ...
```

instead of:

```litex
forall x R:
    =>:
        ...
```

The current `forall ... <=>:` syntax is an exception: if there are no shared hypotheses, keep the required `=>:` block for the left side of the iff.

8. Prefer explicit intermediate equalities and facts over large proof jumps. Each line should be something the verifier can justify from the current context.

9. When a direct algebraic or numeric equality does not verify, first try adding more intermediate equalities instead of looking for a new theorem. Split the proof into small verifier-checkable steps: an algebraic identity, then local simplifications, then the final arithmetic. For example, do not stop at `(3 - 2 * sqrt(2)) * (3 + 2 * sqrt(2)) = 1`; try a chain like `(3 - 2 * sqrt(2)) * (3 + 2 * sqrt(2)) = 3^2 - (2 * sqrt(2))^2 = 9 - 8 = 1`, where the first step is polynomial simplification and later steps use small equalities such as `3^2 = 9` and `(2 * sqrt(2))^2 = 8`.

10. For zero-product arguments, prefer the explicit division step instead of a direct jump. If you know `u * v = 0` and `v != 0`, first write `u = 0 / v`, then close it with `u = 0 / v = 0`. Example: from `(2 * a - b) * (3 * a + b) = 0` and `2 * a - b != 0`, prefer `3 * a + b = 0 / (2 * a - b) = 0` over jumping straight to `3 * a + b = 0`.

11. Keep examples minimal but complete. Include required definitions, assumptions, and imports in the same runnable context.

12. Do not use `know` to hide a proof obligation in an example. Use `know` only when the example is explicitly introducing background mathematics, demonstrating known facts, or stating a deliberately assumed theorem.

## Dataset Translation To Litex

1. When translating a dataset problem into Litex, first reason about the mathematics of the problem before writing Litex code.

2. Do not mechanically translate Lean code, tactic steps, or theorem prover syntax into Litex. Use the source only as reference for the mathematical meaning.

3. After understanding the mathematics, design a Litex formulation that matches the current verifier and proof style of this repository.

4. Prefer the most Litex-native simple formulation as the main checked
   version. A formulation closer to the source text, or closer to Litex's raw
   underlying expression, is secondary unless the user explicitly asks for that
   comparison.

5. The translation process should be iterative: write a small Litex proof, run it, inspect the verifier output, and make the next smallest correction.

6. Before using `know` or `abstract_prop`, first try at least one direct Litex formulation and use verifier feedback to narrow the gap.

7. If part of the formalization is temporarily blocked, it is acceptable to use `know` or `abstract_prop` as a temporary placeholder, but only for the blocked part. Keep the rest of the proof explicit and checkable.

8. Prefer a mathematically natural Litex proof over a source-language-shaped translation. The goal is a verifiable Litex development, not a line-by-line transcription.

## Testing And Verification

1. After changing Rust kernel logic, parser logic, verifier behavior, builtin rules, infer rules, syntax, examples, or documentation snippets, run the smallest relevant test first, then the broader relevant test.

2. Run `cargo test run_examples` after changing `examples/*.lit`, README/docs snippets, or Litex syntax used by examples.

3. Run `cargo test run_the_mechanics_markdown_files` after changing `scripts/The-Mechanics-of-Litex-Proof` snippets or the markdown snippet runner.

4. Run `cargo test run_all` when a change can affect examples and Mechanics snippets together.

5. After changing Litex kernel behavior, including parser, runtime, verifier, builtin rules, infer rules, well-definedness, or output explanation logic, make sure `cargo test run_all` passes before treating the change as complete.

6. If a verifier failure occurs, report the exact file, snippet label, or line shown by the test output before changing code.

7. If any verifier or CLI output looks strange, misleading, too indirect, or hard to understand, report it to the user explicitly. This applies both to error output and to successful `verified_by` / explanation output.

## Documentation Rules

1. Any time you enhance a feature, check whether the documentation needs to be updated. If it does, update it in the same change.

2. If you change Litex syntax or semantics, update the documentation at the same time.

3. If a feature is new, put it into the preview feature section of the documentation.

4. Documentation claims about the verifier should be modest and evidence-based. It is fine to say a proof demonstrates a useful feedback loop; do not imply the theorem is difficult for mature proof assistants unless that is the point being argued.

## Anti-Patterns

1. Do not make markdown examples pass only because prior snippets polluted the environment.

2. Do not add broad abstractions before a repeated pattern is clear.

3. Do not hide proof gaps by weakening examples or skipping tests unless the block is intentionally illustrative.

4. Do not change generated, temporary, or user-edited files unless the task requires it.
