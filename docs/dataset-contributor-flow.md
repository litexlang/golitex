# Dataset Contributor Flow

Use each dataset workspace's top-level `current_data.json` as the public
status contract.  It is intentionally redundant with the source JSONL and
`.lit` files: contributors should be able to see the current state of every
item without knowing the internal split layout.

## Public Entry

Each publishable dataset workspace should expose:

- `current_data.json`: complete generated status index.
- `review.html`: static filter UI for `current_data.json`.
- `README.md`: short queue explanation and regeneration command.
- `todo.md`: local blocker ledger for missing language, stdlib, infer-rule,
  kernel, syntax, diagnostic, or formulation support.

## Statuses

- `checkable`: the item is in a finished/checkable split or has documented
  verifier evidence.  Do not use this status for newly changed items unless
  the relevant Litex verifier command has been run.
- `translated`: a Litex attempt exists, but the current index does not claim
  fresh verification.
- `blocked`: the item has a partial translation or proof attempt with a known
  blocker.
- `missing`: the source item is represented, but no Litex attempt exists yet.

## Contributor Queues

- `write_translation`: pick a missing item, write a natural Litex formulation,
  and keep the source JSON and `.lit` file synchronized.
- `repair_blocked`: start from the current partial proof and blocker label,
  remove the smallest proof debt first, and update the local `todo.md` if a
  missing capability becomes clear.
- `semantic_review`: inspect checkable or translated snippets that may only
  verify an answer object; strengthen them toward a source-to-answer proof
  when feasible.
- `verify_or_audit`: run the relevant verifier batch or classify why the item
  cannot yet be called checkable.
- `quality_review`: inspect rows flagged for `know`, `abstract_prop`, empty
  question text, or other proof-debt markers.
- `human_review`: scan checkable rows for strange source text, bad wording,
  unnatural Litex, or mismatches between the problem and code.

## Work Loop

1. Open `review.html` or filter `current_data.json`.
2. Pick one item id from a queue.
3. Read the source record, existing `litex_code`, matching `.lit` file, and
   nearby blocker notes.
4. Write the mathematical idea before changing code.
5. Make the smallest Litex change and run the smallest relevant verifier
   command.
6. If solved, move the item to the finished split used by that workspace,
   delete the matching unfinished note, and add a short solved note when the
   workspace keeps an experience folder.
7. If still blocked, keep the partial attempt, record the exact failure, and
   put one primary blocker label in the local `todo.md`.
8. Regenerate the status index from the full checkout:

```bash
python3 scripts/build_dataset_current_data.py --dataset <workspace-name>
```

For external-only pull requests where the generator is unavailable, contributors
should update the source record and mention the changed item ids; maintainers
can regenerate `current_data.json` before publishing.
