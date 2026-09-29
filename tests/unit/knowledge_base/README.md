# Unit tests: `knowledge_base`

Loaded from `src/knowledge_base/mod.rs`.

Goldens / `.lit` live under `examples/knowledge_base/`:

| Test module | Example tree |
|-------------|--------------|
| `def_prop/` | `…/def_prop/` |
| `def_abstract_prop/` | `…/def_abstract_prop/` |
| `def_thm/` | `…/def_thm/` |
| `stored_identifier/` | `…/stored_identifier/` |
| `axiom/` | `…/axiom/` |
| `def_struct/` | `…/def_struct/` |
| `mount/` | (temp-dir write/mount; no golden) |
| `json_mini/` | (no example golden) |

Re-dump goldens:

```bash
LITEX_DUMP_KB_FIXTURES=1 cargo test -p litex-lang --lib \
  knowledge_base::unit_tests:: -- dump_fixture --nocapture
```
