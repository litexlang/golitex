# Textbook Draft Workspace

`scripts/textbooks_drafts/<Book>/` is the canonical development surface for
every Litex textbook. Each book directory mirrors the publishable module under
`textbooks/<Book>/`, including its `litex.config`, `.lit` files, `README.md`,
and `math_collections.md`.

The two trees have deliberately different roles:

- Edit and verify `scripts/textbooks_drafts/<Book>/` during ordinary work.
- Treat `textbooks/<Book>/` as the last manually published public snapshot.
- Keep source files, translation records, todos, verifier captures, and
  experience notes in the book's existing working directory, such as
  `scripts/Analysis/`.
- Never automatically refresh an existing draft from `textbooks/`; that could
  overwrite unpublished work.
- Never copy a draft into `textbooks/` unless the user explicitly requests a
  publication or synchronization. Publication remains a manual user action by
  default.

## Initialize a missing draft

Run:

```bash
scripts/textbooks_drafts/init_draft.sh <Book>
```

The command copies `textbooks/<Book>/` only when the corresponding draft does
not exist. It refuses to merge into or overwrite an existing draft.

## Work on a chapter

For a new or existing Chapter 5 whose registered predecessors are Chapters
1--4:

```bash
target/release/litex -compact -session -before \
  scripts/textbooks_drafts/<Book>/chapter05.lit
```

Submit Chapter 5 statements in source order as literal outermost `try:` blocks.
A successful block commits to the session; a failed block rolls back only
itself. Make each successful correction in the draft file, then continue with
the next statement. Use a narrowly documented `trust` only when a real attempt
remains blocked.

Checkpoint the draft chapter with:

```bash
target/release/litex -compact -f \
  scripts/textbooks_drafts/<Book>/chapter05.lit
```

Use a whole-draft gate only at a real book checkpoint:

```bash
target/release/litex -compact -r scripts/textbooks_drafts/<Book>
```

## Prepare a manual publication

Before asking the user to publish:

1. Run the relevant draft chapter gates and the whole-draft gate.
2. Compare `scripts/textbooks_drafts/<Book>/` with `textbooks/<Book>/`.
3. Report the publishable diff and any visible `trust` or other proof debt.
4. Stop. Do not synchronize the trees without an explicit publication request.

