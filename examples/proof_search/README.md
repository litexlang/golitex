# Proof as a search over mathematical knowledge

Litex checks each proposed fact against the current scoped mathematical context.
A successful route combines a rule instance with the evidence required by its
premises. This example makes that interaction visible: an order builtin asks a
membership question, Direct structural membership follows addition, and its
leaves cite an established fact and a closed calculation.

```litex
have x R
0 <= (x + 1)^2
```

Here `have x R` declares that **x is a real number**, recording `x ∈ ℝ` in the
mathematical context.

Open [the interactive figure](index.html) directly in a browser. It works offline
without a server, a Litex installation, external fonts, or network requests.
Use Previous / Next or Play, select a node with a click or Enter/Space, and switch
between English and Chinese. The selected node explains its role and identifies
the corresponding implementation or retained evidence. On narrow screens the
panels stack in reading order.

The [English SVG](proof-search.svg) and [Chinese SVG](proof-search.zh.svg) keep text
editable. Matching PDF and 600-dpi PNG files use the same names and geometry:

| Language | Editable vector | Vector PDF | Raster preview |
| --- | --- | --- | --- |
| English | [SVG](proof-search.svg) | [PDF](proof-search.pdf) | [PNG](proof-search.png) |
| Chinese | [SVG](proof-search.zh.svg) | [PDF](proof-search.zh.pdf) | [PNG](proof-search.zh.png) |

![Proof as a search](proof-search.png)

**Figure: proof as a search over mathematical knowledge.** **a**, A proposed
fact is interpreted in its current mathematical context. The cylinder summarizes
the kinds of indexed knowledge available to readers; the displayed example
concretely establishes `x ∈ ℝ`. **b**, After logical-shape dispatch and
well-definedness checks, the non-equality atomic pipeline tries its permitted
routes in order and returns a successful proof. **c**, The selected even-power
rule requires a real base. Structural addition combines the known membership
of `x` and the calculated membership of `1`. Dashed grey arrows denote required
conditions; solid teal arrows denote returned evidence. The lower flow records
publication after successful top-level checking, followed by direct inference
once and later reuse.

## Meaning and boundaries

- The figure separates **search-stage permissions** from **proof-dependency
  depth**. A rule's premise is checked under its inherited ceiling. Direct
  structural traversal does not reopen the general rule dispatcher.
- The real-addition node is a mathematical closure rule implemented in
  `StructuralMembershipReason::Add`, a Direct route. It is not another nested
  `BuiltinRule` dispatcher call.
- Several proof routes are alternatives for one goal (OR); the premises of a
  selected rule must all hold (AND). The figure displays one actual successful
  dependency, not every possible alternative.
- WD checks may themselves request mathematical evidence. The main mathematical
  dependency is shown separately from those routine formation/domain subtrees.
- The pipeline shown is the **non-equality atomic** route used by the example.
  Equality, compound facts and template membership have their own branches.
- The pipeline order is audited against source, not inferred from a catalogue or
  presented as a recorded sequence of every failed search candidate. The viewer
  is a teaching projection and does not run Litex interactively.
- An accepted fact is stored before direct inference runs once; inferred results
  do not automatically trigger another inference chain. This example's
  `infers` list is empty. Failure to find a proof does not establish falsity.
- This is a standalone explanation of verification, not a replacement for the
  source-first Litex Reading interface.

## Verify and regenerate

From the repository root:

```sh
cargo build --release
target/release/litex -lang en -strict -f examples/proof_search/demo.lit
python3 examples/proof_search/build.py \
  --evidence-dir tmp/proof-search-figure-evidence
```

The builder checks the strict Normal and typed Reading outputs. It requires the
actual selected `EvenPowNonnegative` proof, follows its real-base premise to
`ByStructuralMembership → Add`, checks its `Known` / `Closed` children, and
confirms that the known leaf cites the `have` declaration. It writes compact
provenance and source digests to [acceptance.json](acceptance.json). Raw execution
records remain in the chosen temporary evidence directory.

`build.py` owns the vector layout and both figure languages. It generates the
two SVGs and `index.html` from `index.template.html`; edit those sources rather
than the generated files. `viewer.js` owns only interaction and node explanations;
it does not infer proof relationships. Rebuild after changing the source, layout,
template or viewer. The mathematical snippet is unchanged from the checked
design; any future proof authoring must use the repository's persistent Session
workflow.

To export matching PDFs and PNGs with an optional local Playwright installation:

```sh
node examples/proof_search/export.cjs
```

Set `CHROME_EXECUTABLE` if using an installed Chromium-family browser instead of
Playwright's bundled browser. Browser dependencies are needed only for export;
the checked-in figures and interactive viewer need none. The PNG image dimensions
correspond to 600 dpi at the figure's 183-mm width. SVG and PDF retain text as
text. The layout follows the sans-serif lettering, lower-case panel labels,
editable vector text and restrained decoration described by the
[Nature figure specifications](https://research-figure-guide.nature.com/figures/preparing-figures-our-specifications/)
and [panel/export guide](https://research-figure-guide.nature.com/figures/building-and-exporting-figure-panels/).
It is Nature-inspired artwork, not an affiliation or a guarantee of acceptance.

## Implementation anchors

- [Fact dispatch](../../src/execute/execute_fact_stmt/verify.rs).
- [Non-equality atomic search order](../../src/execute/execute_fact_stmt/verify_atomic_fact/verify_atomic_except_equality/search_atomic_except_equality_fact_proof.rs).
- [Search permissions](../../src/execute/execute_fact_stmt/verify_state.rs).
- [Structural membership](../../src/execute/execute_fact_stmt/verify_atomic_fact/search_structural_membership.rs).
- [Scoped context](../../src/exec_env/README.md).
- [Storage and direct inference](../../src/store_fact_and_infer/README.md).
- [Typed Reading evidence](../../src/reading/README.md).
