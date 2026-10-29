# Task template

## Layout

```text
task/
├── problem.md     the statement, nothing else
├── TASK.md        the exact declaration to produce, plus these rules
├── check          ./check solution.lit  ->  litex -lang en -strict -f
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
- `./check solution.lit` is the only permitted outside command.
- Write one fact, run the check, then add the next fact. Never rewrite an
  accepted line.
- Success: exit 0 and `"errors": []`. Then reply DONE.
```

## Notes

* Give the statement verbatim; a re-stated goal is a different task.
* If the problem needs modelling (geometry, coordinates), say in `problem.md`
  that the agent must choose and justify the model; do not hand it the model.
