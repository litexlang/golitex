---
name: litex-formalizer
description: Formalise and prove a Litex statement (obj, prop, fn, thm) from a natural-language specification, including the definitions it needs. Use when writing or repairing .lit files, when a Litex problem must be formalised from scratch, or when an agent would otherwise read Manual.md or Learn_Litex.md to learn the language.
---

# Litex formalizer

Read `primer.md` first. It is the whole language onboarding: declarations, facts,
moves, the inference boundary, and the constructs that actually break. Do not read
`docs/Manual.md` or `docs/Learn_Litex.md` unless the primer lacks a construct you
need; if that happens, note which construct was missing.

Then follow `task-template.md` for the task layout and the working rules.

## Working rules

1. Write one declaration or fact, run the checker, then write the next one.
2. A rejected line reports `why_failed`. Add the missing fact before it. Never
   rewrite an accepted line.
3. State the goal exactly as given. Do not weaken, rename or reorder the
   statement lines; if they look unprovable, say so instead of changing them.
4. Everything you use must be declared in the file: objects, functions,
   predicates, lemmas. There is no import.
5. Success is `litex -lang en -strict -f <file>` exiting 0 with `"errors": []`,
   not the absence of an obvious error.

## What to report back

* the file path and the exact command you ran,
* every construct you needed that the primer did not cover,
* if the statement turned out to be false or unprovable, the smallest
  counterexample or the blocking obligation, and which statement line was
  responsible.

## Related

* `docs/Litex_Agent_Primer.md` in the repository is the canonical copy of the
  primer.
* `docs/Agent_Prompt_Authoring.md` explains why the primer is shaped this way and
  how to measure a change to it.
* `docs/Litex_Learner_Cheatsheet.md` and `docs/Manual.md` are the human reference.
