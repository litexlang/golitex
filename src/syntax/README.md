# Litex source syntax

This directory owns lexical constants, source names, locations, and formatting
conventions. For example, `forall` is recognized as a reserved keyword, while
`user_name` passes name validation and `__generated` is rejected for user code.

## Examples and boundaries

| Syntax owner | Concrete example |
| --- | --- |
| [`keywords.rs`](keywords.rs) | The parser recognizes source tokens such as `forall`, `have`, `claim`, and `trust`. |
| [`name_types.rs`](name_types.rs) | A theorem name and a predicate name use distinct aliases even when both display as `foo`. |
| [`name_validation.rs`](name_validation.rs) | Rejects reserved keywords and Litex's internal symbol prefix. |
| [`source_conventions.rs`](source_conventions.rs) | Represents a source location as line number plus file path. |
| [`source_formatting.rs`](source_formatting.rs) | Renders lists, braces, indentation, and stored parameter names. |

Syntax code does not parse or verify `1 + 1 = 2`; parsing consumes these
conventions, and output owns JSON, language, and style values.
