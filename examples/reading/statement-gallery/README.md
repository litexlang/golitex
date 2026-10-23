# Statement presentation gallery

A reviewable design for the mathematical detail pane of Litex Reading: one
existing repository example for each of the 52 current statement leaves, plus
nine additional forms of `Fact` (61 examples total).

This is a **presentation prototype**, not 52 newly implemented Reading
projections. The proposed formulas in `designs.json` are curated mathematical
layouts. The examples, accepted statement kinds, highlighted source ranges,
and gray inline inference results come from actual current CLI execution.
Do not advertise the proposed layouts as compiler-generated evidence.

## View locally

From the repository root, using the current release binary:

```sh
python3 examples/reading/statement-gallery/build.py \
  --output tmp/reading-statement-gallery/site
python3 -m http.server 49182 --bind 127.0.0.1 \
  --directory tmp/reading-statement-gallery/site
```

Open <http://127.0.0.1:49182/index.html?gallery=statement-design#DefPropStmt>.
The generated site works offline, with bundled KaTeX, fonts and its MIT license.
No Node runtime or CDN is needed in the browser. Generated sites and raw
execution evidence belong in the task's temporary output, not this directory.

## Presentation

- Select a type from the grouped directory, or the dropdown in a narrow window.
  `Fact` has ten selectable mathematical forms.
- Source stays on the left (above the formulas in a narrow window). The actual
  target statement is blue; its complete proof/definition is retained. Long
  examples scroll within the source pane and initially focus the target.
- The mathematical pane shows only the proposed formulas and any necessary
  scope/assumption qualifier. `prop` keeps every argument, every type and every
  defining clause after ⇔. No prose is inserted into that formula.
- Definition, piecewise function, recurrence, induction, contradiction,
  premise/conclusion and witness layouts are distinct. The `ⓘ` button explains
  the statement's role and the proposed arrangement; it is closed initially.
- Gray results appear on their producer's source line and contain only actual
  published inferred facts. Click one to inspect its retained fact text.
- Explicit user assumptions, axioms and local-only work remain identified.
  An accepted `trust` example is not advertised as a proof of its assumed fact.

The principal examples are the homepage least-squares definition and mean
function, the homepage irrationality proof for √2, and the existing induction
proof of `2^n >= n + 1`. Other types use short existing statement examples.

## Maintenance and validation

`build.py` audits the AST inventory through the existing statement-suite
inventory checker. Primary designs must cover every manifest leaf exactly
once. Each selected source scenario runs once with `-reading -json -e`; its
manifest strict policy is respected. Only accepted targets of the exact
statement kind can be highlighted. Nonzero exits, failed runs, missing target
kinds and timeouts fail the build. The displayed evaluation result is also
checked against the actually published equality.

The builder copies source examples without rewriting their mathematics. A new
or repaired `.lit` example still requires the repository's normal persistent
Session authoring workflow; the builder is a baseline/final checker, not an
iterative authoring loop. Public examples must not depend on local `scripts/`.

`acceptance.json` records the reviewed design digest and focused validation.
The generated site's own acceptance file records the binary and source hashes
for that particular build. Changing a display in `designs.json` requires
mathematical review as well as TeX parsing; a renderable formula alone is not
evidence that the meaning is correct.
