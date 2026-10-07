# Mathematical dependency graphs

`litex -graph -e/-f/-r` exports definitions, theorems and accepted facts.
`by thm`, `by def`, search routes, WD checks and other execution actions are
not nodes. A theorem application connects the reusable theorem directly to
its resulting fact; source details stay on the edge. Inferred and local facts
are folded by default in the viewer.

```sh
litex -graph -strict -f examples/stmt_nodes/graph/math_dependencies.lit > graph.json
python3 src/graph/render_html.py graph.json graph.html
```

Open `graph.html`, or open `docs/assets/math_graph_viewer.html` and select a
JSON file. The viewer supports selection, dependency/source details, search,
and expansion of inferred and local facts. It has no network or third-party
runtime dependency.

## Data and boundaries

Schema version 1 uses English field/type keys independent of `-lang`:

- `kind: math_graph`, `schema_version`, `success`, `partial`, `target`, `path`.
- Nodes: `id`, `kind` (`definition`, `thm`, `fact`), `label`, `statement`,
  `source`, `line`, `scope`, `origin`, `inferred`, `published`,
  `history_available`, `default_visible`.
- Edges: `from`, `to`, `kind`, `dependency_group`, original `statement` and
  `source`. The viewer folds repeated edges; data retains their groups.
- `diagnostics` and a derived `mermaid` view.

`definition_reference` and `uses_definition` describe structured vocabulary
use, not logical implication. `depends_on` records actual fact citations;
`theorem_instance` connects a theorem to a checked instance; `inferred_from`
records a store/infer batch. A group belongs to an accepted statement/batch
and retains its premises; it does not claim a minimal independent proof for
every atomic output. There are no time-order edges. Repeated theorem calls
share the same declaration node.

FactIds and scope IDs are run-local. Source/module ownership and bound IDs
remain distinct when terminal names or physical filenames coincide. Aliases
of one imported module converge on its owner. Bindings and citations come
from typed AST/evidence and existing environments, not localized JSON or
mathematical display strings.

`history_available` means dependency/source history was captured in this run;
it does not promise a serialized full certificate or independent replay.
Cached declarations can expose interfaces while their original proof history
is unavailable. `origin` distinguishes trust, axioms/foundation interfaces,
local assumptions, local facts and external records. Successful verification
does not alone establish that a fact has no trust dependencies.

Failed statements add diagnostics, not accepted nodes. In an aborted file,
earlier successful statements remain historical results with
`published: false`. Local facts stay scoped. Missing proof history is not
reconstructed from a fact inventory. A search miss does not prove falsity.

## Ownership and maintenance

`run/run_graph.rs` selects graph output at the CLI boundary and delegates to
ordinary launch commands. Public runner APIs retain capture-disabled wrappers.
Opt-in callbacks read results while file environments are alive, before the
existing finish/abort operations. The exporter changes no Runtime/ExecEnv/AST
shapes, ID counters, proof search or module cache policy.

Regenerate the exhaustive typed visitor after producer changes:

```sh
python3 src/graph/generate_walk.py
python3 src/graph/generate_walk.py --check
cargo test --release --lib graph::tests
```

The generator distinguishes subject IDs from citations, skips failed evidence
and reads retained local contexts without merging them. A freshness test
protects added producer fields/variants. Generation handles the many current
rule-specific evidence payloads; dependencies use no runtime reflection or
JSON decoding.

The durable tracer and preview are in `examples/stmt_nodes/graph/`. Tests check
real citations, command-node absence, scope, failed rollback, trust, locale,
prefix loading and cold/cached import aliases.
