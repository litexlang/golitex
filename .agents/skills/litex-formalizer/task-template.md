# Task template

## Layout

```text
task/
├── problem.md     the statement, nothing else
├── TASK.md        the exact declaration to produce, plus these rules
├── step           incremental check: ./step  (keeps a live session)
├── check          whole-file gate: ./check solution.lit
└── solution.lit   the artifact (single file, no imports)
```

## TASK.md

```markdown
# Task

Formalise and prove the statement in `problem.md` in Litex.

Write a single file `solution.lit`. Every object, predicate, function and lemma
you need must be written by you in that file; nothing is provided. State the
result with `thm`.

The declaration must be exactly:

```litex
<the declaration, verbatim>
```

Do not change these lines. Check with `./check solution.lit`; success means exit
code 0 and `"errors": []`.
```

## Prompt around it

```text
Read problem.md and TASK.md, then do the task.

Rules:
- Work only inside this directory.
- Do not change the statement lines.
- Append to `solution.lit`, then run `./step`; it checks only what is new and
  prints one line. Never re-check the whole file after every line.
- Never rewrite an accepted line. `RESYNC` means the whole file was re-checked.
- Finish with `./check solution.lit`; success is exit 0 and `"errors": []`.
```

## Notes

* Give the statement verbatim; a re-stated goal is a different task.
* If the problem needs modelling (geometry, coordinates), say in `problem.md`
  that the agent must choose and justify the model; do not hand it the model.
