# Analysis I book workspace

The runnable source of Tao's *Analysis I* translation is this directory:
`textbooks/Analysis`.  Edit chapter and cite `.lit` files here; run a chapter
with `target/debug/litex -f textbooks/Analysis/chapN.lit`, or the project
entrance with `target/debug/litex -r textbooks/Analysis`.

The authoring tools deliberately remain in `scripts/analysis-one`:

- `AGENT.md` and `style_guide.md` are the writing rules;
- `todo.md` and `todo/` are the canonical blocker and experience records.

Do not recreate the retired pre-textbooks Analysis source tree.
Historical todo and experience notes may mention that former path; those
references describe the pre-move workspace rather than the current source.

For proof work, follow the persistent-REPL workflow in the shared Analysis
instructions.  Keep source-facing `trust` and `abstract_prop` visible, and
update the concise end-of-file audit comment whenever their status changes.
