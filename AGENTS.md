# Litex Local Instructions

Always apply these rules when working in this repository.

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

2. Do not rely on external mathematical libraries when writing Litex examples unless the user explicitly asks for that. Prefer proof steps that the current Litex verifier can check directly.

3. Make documentation and Mechanics of Litex Proof `litex` fenced blocks self-contained. A snippet should not depend on a previous snippet sharing the same environment. If a block is illustrative only, mark it with `<!-- litex:skip-test -->`.

4. Any time the user asks for code that makes some Litex code verifiable, write the Litex code in `examples/tmp.lit` and test it, so the user can run it directly.

5. When writing ordinary Litex `forall` facts, do not write an empty implication body. Write:

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

6. Prefer explicit intermediate equalities and facts over large proof jumps. Each line should be something the verifier can justify from the current context.

7. Keep examples minimal but complete. Include required definitions, assumptions, and imports in the same runnable context.

8. Do not use `know` to hide a proof obligation in an example. Use `know` only when the example is explicitly introducing background mathematics, demonstrating known facts, or stating a deliberately assumed theorem.

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
