# Shared kernel utilities

This directory holds small cross-subsystem values such as `FactId::new(12) -> f12`, the keyword `forall`, and the output language `zh`.

## Examples and boundaries

| Utility | Concrete example |
| --- | --- |
| [`fact_id.rs`](fact_id.rs) | Stored facts receive runtime-unique IDs such as `f1` and `f2`; equal display text does not merge those IDs. |
| [`keywords.rs`](keywords.rs) | The parser recognizes source tokens such as `forall`, `have`, `claim`, and `trust`. |
| [`name_types.rs`](name_types.rs) | A theorem name and a predicate name use distinct aliases even when both display as `foo`. |
| [`output_language.rs`](output_language.rs) | `-lang zh` selects Simplified Chinese output such as `验证错误`. |
| [`json_value.rs`](json_value.rs) | Runner output renders `JsonValue::Bool(true)` as JSON `true`. |
| [`count_range_integer.rs`](count_range_integer.rs) | The closed interval `1...3` contains the three integers `1`, `2`, and `3`. |

`common` does not verify `1 + 1 = 2`; it supplies values such as `FactId` and `JsonValue` to the verifier and output modules that do.
