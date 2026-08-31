# Structural JSON and human output

For `1 + 1 = 2`, statement-result JSON v2 reports `"outcome": "success"` and keeps `RationalNormalization` inside the recursive proof object.

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

Start with [`result_json_v2/renderer/model.rs`](result_json_v2/renderer/model.rs)
for the stateful structural-JSON visitor and
[`result_json_v2/renderer/statement_dispatch.rs`](result_json_v2/renderer/statement_dispatch.rs)
for its top-level dispatch. Each result family has a named renderer beside
those files; for example, fact verification, object well-definedness, proof
blocks, and theorem statements do not share one catch-all implementation file.
The stateless encoders live in
[`result_json_v2/helpers.rs`](result_json_v2/helpers.rs), and the black-box
structural JSON regressions live in
[`tests/integration/result_json_v2.rs`](../../tests/integration/result_json_v2.rs).

Localization follows the same boundary:
[`localization/rendering.rs`](localization/rendering.rs) selects and formats a
message, while [`localization/translations/`](localization/translations) owns
one source file per language. Use
[`success_rendering.rs`](success_rendering.rs) and
[`runtime_error_rendering.rs`](runtime_error_rendering.rs) for human-facing
rendering examples.
