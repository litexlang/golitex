# new_pipeline knowledge_base examples

Dedicated example tree for **persisting / restoring** module products
(`__litex_knowledge_base__` / KB codecs). Not a substitute for
`stmt_nodes/` proof tracers — those exercise `exec_stmt`; this tree exercises
**what gets written to disk** and how it looks.

```text
examples/new_pipeline/knowledge_base/
  README.md                 (this file)
  def_prop/                 first codec: one DefPropStmt ↔ JSON
    is_pos.lit              source prop
    is_pos.def_prop.json    committed store artifact (golden)
    README.md
```

White-box Rust tests live under
`tests/unit/new_pipeline/knowledge_base/` and **load goldens from this
examples tree** (single source of truth for “what store looks like”).

## Acceptance (def_prop)

1. Litex still runs the `.lit` (definition works):

```bash
LITEX_NEW_PIPELINE=1 target/release/litex -f \
  examples/new_pipeline/knowledge_base/def_prop/is_pos.lit
```

2. Codec round-trip / golden match (Rust):

```bash
cargo test -p litex-lang --lib new_pipeline::knowledge_base::
```

Re-dump the JSON golden after intentional codec changes:

```bash
LITEX_DUMP_KB_FIXTURES=1 cargo test -p litex-lang --lib \
  new_pipeline::knowledge_base::unit_tests::def_prop::tests::dump_is_pos_fixture \
  -- --exact --nocapture
```

## Note on ids

`is_pos.def_prop.json` freezes illustrative `IdentifierId` / `FactId` values
for a stable golden. A live `-f` run allocates different session ids; the
**.lit** checks math, the **.json** checks the store shape + codec.
