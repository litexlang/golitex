# Dataset Translation

For MATH500, miniF2F, high-school, GSM8K, Math23K, Mechanics, or textbook work:

1. Read the natural-language problem and solution.
2. Choose the most Litex-native simple formulation that matches the current
   verifier. Do not prefer source theorem prover syntax, source-text shape, or
   lower-level raw Litex expression shape unless the user explicitly asks for
   that comparison.
3. Start with a small statement/proof skeleton.
4. Run the verifier.
5. Repair locally until checkable or blocked.
6. Record status and blocker labels near the source folder.

## Translation Item Contract

For every newly created or touched dataset, textbook, contest, exam,
Mechanics, or generated-math item, maintain a compact structured item record
with this shape:

```yaml
source:
problem:
proof_idea:
litex_code:
comments:
```

Field meanings:

- `source`: dataset, book, exam, contest, or source name.
- `problem`: source problem, theorem, exercise, or a reusable reformulation if
  the source text cannot be redistributed.
- `proof_idea`: the mathematical idea before Litex code.
- `litex_code`: the current runnable or intended Litex code.
- `comments`: verifier command, proof-attempt notes, blocker label, source or
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

Useful status concepts:

- `translated`: natural Litex statement/proof attempt exists.
- `checkable`: verifier accepts it with no unwanted proof debt.
- `blocked`: failure reason is understood and has a minimal reproduction.

Do not present answer-only snippets as full formalizations unless the benchmark policy explicitly says answer checking is the task.
