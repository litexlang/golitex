# def_prop store example

Surface source and the JSON a `store_def_prop` snapshot looks like.

## Source (`is_pos.lit`)

```litex
prop is_pos(x R):
    x > 0

$is_pos(1)
```

Run:

```bash
litex -f examples/new_pipeline/knowledge_base/def_prop/is_pos.lit
```

## Stored artifact (`is_pos.def_prop.json`)

Hand-written / codec golden for one `DefPropStmt` (kind `def_prop`).
Same bytes are asserted by
`tests/unit/new_pipeline/knowledge_base/def_prop/` against `store_def_prop`.

This is the “can we save it?” answer: **yes — as this JSON file**, then
`load_def_prop` / `read_def_prop` brings it back.
