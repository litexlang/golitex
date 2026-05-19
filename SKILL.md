---
name: litex
description: Write, check, explain, and debug Litex proof code. Use when working with .lit files, Litex syntax, formalized everyday mathematics, proof scripts, objects, facts, statements, or when generating examples for the Litex language.
disable-model-invocation: true
---

# Litex Skill

Use this skill when writing, checking, explaining, or debugging Litex proof code. Download this SKILL.md here: https://github.com/litexlang/golitex/blob/main/SKILL.md

Litex is a fact-oriented formal language for everyday mathematics. Users write mathematical facts; Litex grows a verified context by checking those facts, storing accepted facts, inferring routine consequences, and explaining how accepted facts were proved.

## Read First

If this skill is inside the `golitex` repository, prefer local files:

- `docs/Manual.md`
- `docs/Setup.md`
- `docs/Preview_Features.md`
- `docs/litex_cheatsheet.md`
- `examples/`

If this skill was copied outside the repository, use the GitHub sources:

- Manual: https://github.com/litexlang/golitex/blob/main/docs/Manual.md
- Setup: https://github.com/litexlang/golitex/blob/main/docs/Setup.md
- Preview features: https://github.com/litexlang/golitex/blob/main/docs/Preview_Features.md
- Cheatsheet: https://github.com/litexlang/golitex/blob/main/docs/litex_cheatsheet.md
- Examples: https://github.com/litexlang/golitex/tree/main/examples
- Repository: https://github.com/litexlang/golitex

## Core Mental Model

Litex code is organized around:

- Objects: mathematical things such as numbers, sets, tuples, functions, ranges, matrices, and named values.
- Facts: claims about objects, such as `x = 2`, `x $in R`, `$is_set(A)`, or `$prime(n)`.
- Statements: proof-script actions that define objects, assert facts, open proof blocks, split cases, provide witnesses, or store known information.
- Verification: checking whether a fact follows from the current context, definitions, builtin rules, known facts, and known `forall` facts.
- Execution: growing the verified context as accepted facts are stored and inference adds routine consequences.

In Litex, users usually state the target fact instead of choosing a tactic for it. The checker tries to match that fact against builtin rules, known facts, and known `forall` facts. Choose statement forms that expose the right information for matching: chains for transitive/order reasoning, `by cases` for recognized case splits, `have by exist` to extract witnesses, `witness` to close existential goals, and explicit intermediate facts when matching needs help.

## Writing Litex Code

When asked to write Litex code:

1. Read nearby examples before inventing syntax.
2. Prefer stable syntax from `docs/Manual.md`.
3. Check experimental syntax in `docs/Preview_Features.md`.
4. If the `litex` command is not available, read `docs/Setup.md` or https://github.com/litexlang/golitex/blob/main/docs/Setup.md before running code.
5. Create a small temporary `.lit` file for runnable code; inside this repository, `examples/tmp.lit` is the default scratch file unless the user asks for another path.
6. Run `litex -f path/to/file.lit` or `cargo run -- -f path/to/file.lit`.
7. Use English comments in `.lit` files.
8. Do not invent unsupported tactics, keywords, or object forms.

## Style Guidelines

Prefer ordinary mathematical steps over proof-engine cleverness.

Good Litex code should:

- State useful intermediate facts explicitly.
- Use builtin objects and predicates when they express the idea.
- Keep proof steps close to everyday mathematical writing.
- Use `forall`, `exist`, `claim`, `prove`, `by cases`, `by induc`, and related statements in the style shown by existing examples.
- Treat `unknown` as a request for a smaller intermediate fact, domain condition, equality, membership fact, or lemma.

## Preview Features

Preview features are usable experiments. Their syntax and semantics may change.

Before using preview syntax, read:

- Local: `docs/Preview_Features.md`
- GitHub: https://github.com/litexlang/golitex/blob/main/docs/Preview_Features.md

Examples include structs, struct parameters, field access, `by struct`, `by transitive_prop`, and `by symmetric_prop`.

## Testing Checklist

After generating or editing Litex code:

1. Put a small runnable example in a temporary `.lit` file.
2. Run `cargo run -- -f path/to/file.lit`.
3. If changing Rust implementation, run `cargo check`.
4. If changing language behavior or docs examples, run `cargo test`.
5. If syntax or semantics changed, update docs or preview docs.

## Important Boundaries

Do not assume Litex is Lean, Coq, Isabelle, or a tactic language.

In Litex:

- Facts are not ordinary objects.
- A term such as `x + 1` is an object, not a fact.
- A fact becomes useful after it is verified and stored.
- Known `forall` facts are reused by matching and substitution.
- Builtin mathematical background handles many routine relationships.
- Preview features should not be treated as stable unless the docs say so.
