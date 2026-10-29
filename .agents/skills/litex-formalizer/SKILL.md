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

1. Work incrementally. Append one declaration (or a few related facts) to
   `solution.lit`, then run `./step`. It keeps a live session and checks only the
   new statements, so it costs milliseconds and prints one line. Never re-run a
   whole-file check after every line: that re-checks and re-prints the entire
   file, which is the main way a Litex session becomes expensive.
2. A rejected line reports `why_failed`. Add the missing fact before it. Never
   rewrite an accepted line. If `./step` prints `RESYNC`, you rewrote earlier
   lines and the whole file was re-checked; prefer appending.
3. `./check solution.lit` is the whole-file strict gate: run it once before you
   report success.
3. State the goal exactly as given. Do not weaken, rename or reorder the
   statement lines; if they look unprovable, say so instead of changing them.
4. Everything you use must be declared in the file: objects, functions,
   predicates, lemmas. There is no import.
5. Batch a few related statements per `./step` call when they are independent;
   the checker reports the first failing statement.
6. Structure the file so you append: objects, functions and predicates first,
   then helper lemmas, then the theorem. Inserting a lemma above accepted text
   forces a session reset and re-checks the whole file.
6. Success is `./check solution.lit` exiting 0 with `"errors": []`, not the
   absence of an obvious error.

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
