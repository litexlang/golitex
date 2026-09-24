# Unit tests: `new_pipeline::knowledge_base`

Loaded from `src/new_pipeline/knowledge_base/mod.rs` via:

```rust
#[cfg(test)]
#[path = "../../../tests/unit/new_pipeline/knowledge_base/mod.rs"]
mod unit_tests;
```

| Path | Covers |
|------|--------|
| `def_prop/` | `store_def_prop` / `load_def_prop` / file write-read |
| `json_mini/` | Hand-rolled JSON Value round-trip |

**Goldens and `.lit` sources** live under the example tree (not here):

`examples/new_pipeline/knowledge_base/`

Def-prop tests `include_str!` /
re-dump that tree’s `def_prop/is_pos.def_prop.json`.

## Regenerate example golden

```bash
LITEX_DUMP_KB_FIXTURES=1 cargo test -p litex-lang --lib \
  new_pipeline::knowledge_base::unit_tests::def_prop::tests::dump_is_pos_fixture \
  -- --exact --nocapture
```
