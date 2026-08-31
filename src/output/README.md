# Structural JSON and human output

For `1 + 1 = 2`, statement-result JSON reports `"outcome": "success"` and keeps `RationalNormalization` inside the recursive proof object.

```json
{
  "outcome": "success",
  "result": {
    "kind": "Fact",
    "statement": "1 + 1 = 2",
    "verification": {"kind": "AtomicFact", "proof": {"kind": "BuiltinRule"}}
  }
}
```

## Examples and boundaries

| Input/mode | Output behavior |
| --- | --- |
| `1 + 1 = 2` | Emits the statement, proof, well-definedness, store, inference, and phase fields. |
| `-e '1 = 1'` | Uses the one canonical detailed CLI projection. |
| `-lang zh -e '1 = 2'` | Keeps machine keys stable and localizes human-readable messages and labels. |
| Two references to one shared proof Result | Use `$id`/`$ref` rather than flattening two copies. |

Start with [`statement_result/renderer/state.rs`](statement_result/renderer/state.rs)
for the stateful structural-JSON visitor and
[`statement_result/renderer/statement_dispatch.rs`](statement_result/renderer/statement_dispatch.rs)
for its top-level dispatch. Each result family has a named renderer beside
those files; for example, fact verification, object well-definedness, proof
blocks, and theorem statements do not share one catch-all implementation file.
The stateless encoders live in
[`statement_result/helper.rs`](statement_result/helper.rs), and the black-box
structural JSON regressions live in
[`tests/integration/statement_result_json.rs`](../../tests/integration/statement_result_json.rs).

Runtime errors have their own renderer in
[`runtime_error/rendering.rs`](runtime_error/rendering.rs). Human-readable
message translation lives in [`messages/rendering.rs`](messages/rendering.rs),
while [`messages/catalogs/`](messages/catalogs) owns one message catalog per
language. Machine-readable JSON keys remain stable across languages.
