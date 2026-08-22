# Structural JSON and human output

For `1 + 1 = 2`, statement-result JSON v2 reports `"outcome": "success"` and keeps `RationalNormalization` inside the recursive proof object.

```json
{
  "schema": "litex.statement-result.v2",
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
| `-compact -e '1 = 1'` | Reduces success display while retaining full error diagnostics. |
| `-detail -e '1 = 1'` | Includes detailed audit fields and raw source paths. |
| `-lang zh -e '1 = 2'` | Localizes error keys and text; for example, `VerifyError` becomes `验证错误`. |
| Two references to one shared proof Result | Use `$id`/`$ref` rather than flattening two copies. |

Start with [`result_json_v2.rs`](result_json_v2.rs) for structural JSON and [`success.rs`](success.rs) / [`error.rs`](error.rs) for human-facing examples.
