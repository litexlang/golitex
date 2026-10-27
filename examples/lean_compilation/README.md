# From checked evidence to Lean

An offline interactive explanation and editable journal-style figure of one
real Litex-to-Lean compilation. The example makes **proof-route preservation**
visible: the objects, construction conditions, selected proof and citations
checked by Litex determine the emitted Lean terms.

Open [the interactive view](index.html?lang=en), then select a node or advance
the five stages. The top walkthrough and left flow share the same stage names,
numbers and selection: source/verification, typed results, replay compiler,
generated Lean, and Lean checking. Evidence nodes are selectable details within
their owning stage. The evidence subtree, generated code and semantic declaration
change together. The view includes all its data locally and needs no network.
The complete viewer is `index.html`. Opening the editable `index.template.html`
forwards to that viewer; a visible link remains available if scripts are disabled.
The mathematical statement and its Litex source stay visible in the trace area,
including the final Lean-check step; that step summarizes the same statement's
checks and keeps the full technical receipt in the verification disclosure.
The [definitions-and-proofs example](../proof_search/README.md) introduces the
earlier verification stage.

## One fact, one recorded route

The existing [source](../../lean/examples/add_zero/statement.lit) says:

```litex
forall a C:
    a + 0 = a
```

The recorded result introduces a complex member, stores its membership as
`f15`, checks both addition operands, and selects this actual equality route:

```json
"searched_proof": {
  "type": "builtin_rule",
  "rule": "Calculation",
  "mode": "rational"
}
```

See the [complete Detailed snapshot](trace.detailed.json). IDs belong to this
captured run; they are not permanent names for mathematical propositions.

The [actual generated file](../../lean/examples/add_zero/statement.lean) retains
`h_15`, constructs the sum with `Litex.add`, and compiles the rational route
through native numeric observations and `Litex.NativeBridge.sameOfDenoteNumber`.
The emitted `(by ring!)` is a fixed normalization check within that selected
adapter. It produces a proof checked by Lean. It does not replace the selected
route with the separately available `Litex.addZero` theorem.

## Where JSON fits

```text
source → Runtime → typed results → compiler → generated Lean → Lean check
                       ↓             ↑
                  Detailed JSON      completed Runtime: exact-ID resolution
```

The current compiler consumes Rust typed results, plus the completed Runtime
for citation resolution. Detailed JSON presents the same evidence for
inspection; a saved JSON file is not currently accepted as a standalone replay
input. Normal CLI JSON does not include every child proof. Detailed projection
is a Rust API, not a `-detailed` CLI flag.

The capture used for this example projects Detailed JSON and compiles the
**same successful result with the same completed Runtime**. The public
`-strict -lean -f` command independently produces identical bytes. This
explainer is a viewer and figure builder; it adds no compiler or JSON importer.

## What `Litex.lean` does

[The semantic library](../../lean/Litex.lean) supplies:

- **Objects and construction conditions.** `Obj α` contains a value and its
  WD evidence. `Representation M α` gives its fixed denotation. An object stays
  generic; proving membership in `C` does not retype it as native `ℂ`.
- **Mathematical meanings.** `In a A` is membership of the denotations;
  `Same a b` is equality of denotations. The interpretation `M : Semantics`
  carries the required laws and remains explicit in the generated theorem.
- **Proved bridges.** `NativeBridge.sameOfDenoteNumber` consumes numeric
  denotation witnesses and a native equality to prove `Same` of the original
  objects. These are Lean proofs, rather than an unchecked rule-name lookup.
- **Proof packaging.** `litex_complete` and `litex_checked_step` close/package
  the supplied generated proofs and reject open goals.

`import Litex` makes that API available to generated Lean. Lean elaborates the
code into proof terms and checks them with its kernel. Generation alone does
not run that check. This example's theorem remains conditional on its explicit
interpretation laws; the diagram does not assert a model for every Litex rule.

A separate handwritten Adapter may instantiate a reviewed interpretation and
convert the generated interface into an ordinary Lean/Mathlib statement. The
[adding-zero walkthrough](../../docs/examples/litex_to_lean/add_zero/README.md)
shows that further step. It is not automatic output of this compiler demo.

## Figures and reproducibility

| Language | Editable vector | Print | 600-dpi raster |
|---|---|---|---|
| English | [SVG](lean-compilation.svg) | [PDF](lean-compilation.pdf) | [PNG](lean-compilation.png) |
| Chinese | [SVG](lean-compilation.zh.svg) | [PDF](lean-compilation.zh.pdf) | [PNG](lean-compilation.zh.png) |

`build.py` regenerates both figures and the offline page from the checked
snapshot, existing canonical source/generated pair and semantic-library excerpts:

```sh
python3 examples/lean_compilation/build.py
```

It checks the source, generated-file and semantic-library hashes before using
the snapshot. After any of those changes, refresh the focused compiler/Lean
capture before rebuilding the presentation. It never generates Lean itself.
`export.cjs` optionally uses local Playwright/Chromium to export the SVGs as
vector PDFs and high-resolution PNGs; `CHROME_EXECUTABLE` can select a browser.

The [acceptance record](acceptance.json) and [compiler evidence](evidence.json)
record strict verification, same-result capture, byte equality, pinned
Lean/Mathlib checking and artifact hashes. On 2026-10-27, both the current
semantic library and this generated pair were freshly kernel checked with
Lean 4.31.0. The theorem's axiom audit reported only `propext`,
`Classical.choice`, and `Quot.sound`; no proof holes were introduced.

## Reading the trace

The figure abbreviates code labels; the interactive code pane shows the
excerpts in full. Selecting a node connects the actual Detailed evidence,
emitted Lean code and relevant semantic-library declaration. The sections
above explain how those three layers relate, including the separate Adapter
step needed for an ordinary Lean/Mathlib interface.
