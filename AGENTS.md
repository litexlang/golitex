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

Classify blockers explicitly. Useful blocker labels include:

1. `blocked_by_language`: Litex cannot naturally express the object,
   binding structure, or proposition yet.

2. `blocked_by_stdlib`: the proof needs missing definitions, lemmas, or
   theorem organization.

3. `blocked_by_infer_rule`: the mathematical step is simple but needs a new
   infer rule or builtin rule.

4. `blocked_by_kernel`: the verifier, runtime, well-definedness logic, or
   core proof model is missing required behavior.

5. `blocked_by_syntax`: the parser or syntax makes the intended expression
   awkward or impossible.

6. `blocked_by_diagnostics`: the verifier output is too indirect, confusing,
   or misleading to support a tight feedback loop.

7. `blocked_by_formulation`: the source statement needs a more natural Litex
   formulation rather than a mechanical translation.

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

## Litex Language And Proof Style

1. Litex examples should expose a tight verifier feedback loop: write a small proof, run it, read the exact verifier output, and make the next smallest correction until the proof is checkable.

2. Before writing Litex code, first explain the proof idea in natural language and look for the local proof pattern. Prefer starting from the mathematical move that should work in Litex rather than searching for theorem names as if the task were Lean.

3. Do not rely on external mathematical libraries when writing Litex examples unless the user explicitly asks for that. Prefer proof steps that the current Litex verifier can check directly.

4. Make documentation and Mechanics of Litex Proof `litex` fenced blocks self-contained. A snippet should not depend on a previous snippet sharing the same environment. If a block is illustrative only, mark it with `<!-- litex:skip-test -->`.

5. Any time the user asks for code that makes some Litex code verifiable, write the Litex code in `examples/tmp.lit` and test it, so the user can run it directly.

6. When writing ordinary Litex `forall` facts, do not write an empty implication body. Write:

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

7. Prefer explicit intermediate equalities and facts over large proof jumps. Each line should be something the verifier can justify from the current context.

8. When an agent cannot prove a direct algebraic or numeric equality, first try adding more intermediate equalities instead of looking for a new theorem. Split the proof into small verifier-checkable steps: an algebraic identity, then local simplifications, then the final arithmetic. For example, do not stop at `(3 - 2 * sqrt(2)) * (3 + 2 * sqrt(2)) = 1`; try a chain like `(3 - 2 * sqrt(2)) * (3 + 2 * sqrt(2)) = 3^2 - (2 * sqrt(2))^2 = 9 - 8 = 1`, where the first step is polynomial simplification and later steps use small equalities such as `3^2 = 9` and `(2 * sqrt(2))^2 = 8`.

9. For zero-product arguments, prefer the explicit division step instead of a direct jump. If you know `u * v = 0` and `v != 0`, first write `u = 0 / v`, then close it with `u = 0 / v = 0`. Example: from `(2 * a - b) * (3 * a + b) = 0` and `2 * a - b != 0`, prefer `3 * a + b = 0 / (2 * a - b) = 0` over jumping straight to `3 * a + b = 0`.

10. Keep examples minimal but complete. Include required definitions, assumptions, and imports in the same runnable context.

11. Do not use `know` to hide a proof obligation in an example. Use `know` only when the example is explicitly introducing background mathematics, demonstrating known facts, or stating a deliberately assumed theorem.

## Dataset Translation To Litex

1. When translating a dataset problem into Litex, first reason about the mathematics of the problem before writing Litex code.

2. Do not mechanically translate Lean code, tactic steps, or theorem prover syntax into Litex. Use the source only as reference for the mathematical meaning.

3. After understanding the mathematics, design a Litex formulation that matches the current verifier and proof style of this repository.

4. The translation process should be iterative: write a small Litex proof, run it, inspect the verifier output, and make the next smallest correction.

5. Before using `know` or `abstract_prop`, first try at least one direct Litex formulation and use verifier feedback to narrow the gap.

6. If part of the formalization is temporarily blocked, it is acceptable to use `know` or `abstract_prop` as a temporary placeholder, but only for the blocked part. Keep the rest of the proof explicit and checkable.

7. Prefer a mathematically natural Litex proof over a source-language-shaped translation. The goal is a verifiable Litex development, not a line-by-line transcription.

## Testing And Verification

1. After changing Rust kernel logic, parser logic, verifier behavior, builtin rules, infer rules, syntax, examples, or documentation snippets, run the smallest relevant test first, then the broader relevant test.

2. Run `cargo test run_examples` after changing `examples/*.lit`, README/docs snippets, or Litex syntax used by examples.

3. Run `cargo test run_the_mechanics_markdown_files` after changing `The-Mechanics-of-Litex-Proof` snippets or the markdown snippet runner.

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
