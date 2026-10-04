# Template aliases and struct tuple values

Task: the 2026-10-04 follow-up asking for a local repair of `chosen_struct.first = 1` when the value comes from a template/alias chain. Repair ownership: local Rust semantic repair. This closes the template-composition item from the 2026-10-03 migration audit.

## Before

With the Triple and template declarations from the [original example](../../../stmt_nodes/definition/let_template_struct_aliases.lit):

```litex
# let triple_R = \triple<R>
# let chosen = \triple<R>(1, 2, 3)
# triple_R(4, 5, 6) = (4, 5, 6)
# chosen = (1, 2, 3)
# have chosen_struct &Triple<R> = chosen
# chosen_struct.first = 1
```

The alias application failed WD with `no matching function signature`; the chosen-value and field equalities failed proof search. Direct typed literal projection passed. The failure was callable/value composition, not a missing field-to-coordinate mapping.

## Now

The same prefix passes in the [dedicated runnable tracer](../../../stmt_nodes/definition/template_alias_struct_tuple.lit). Its second case also verifies a two-level function alias and all three struct coordinates without first asserting a complete tuple equality:

```litex
let another_triple_R = triple_R
let raw_chosen = another_triple_R(7, 8, 9)
have raw_struct &Triple<R> = raw_chosen
raw_struct.first = 7
raw_struct.second = 8
raw_struct.third = 9
```

These excerpts share the declarations in the linked tracer; the exact self-contained tracer, not this Markdown excerpt, was run. Callable WD and codomain lookup read checked template declarations through stored head equalities. Tuple-value lookup follows stored object equalities and performs one checked tuple-body substitution. The existing struct bridges still map fields to one-based coordinates. Evidence retains the head/subject equality paths, instantiated declaration and competing signature matches; the readers publish no facts and enable no further search stages.

## Evidence and boundary

- `target/release/litex -strict -f examples/stmt_nodes/definition/template_alias_struct_tuple.lit`: exit 0, `success: true`, no session error.
- 49 focused release Rust tests pass: known tuple 14, application WD evidence 3, template definition 10, callable special-property 8, JSON acceptance 14. The renamed `run_examples_template_aliases_and_named_results_retain_tuple_value_paths` also passes its focused harness gate.
- 16 strict CLI cases have the expected outcomes: six positive cases, nine false-value/type/domain/guard/arity rejections, and the independent one-field parser rejection. The touched Manual snippet also passes a strict `-e` gate.
- Wrong field values, tuple order/length, parameter carriers and missing template/function guards remain rejected. Nested function bodies are not recursively unfolded by this reader.
- The full original example still rejects its later one-field `ScalarOps` definition. One-field representation and unrelated symbolic finiteness remain open; this task makes no full-system or Lean-export claim.

Exact sources, binary/source hashes, former failures, acceptance JSON and Rust transcripts are in the [proof journal](../../proof_journals/template-alias-struct-tuple-2026-10-04.json).
