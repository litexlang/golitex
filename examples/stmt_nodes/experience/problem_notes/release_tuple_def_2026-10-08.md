# Tuple release acceptance — 2026-10-08

`release tuple def object` now publishes a checked exact finite-sequence membership and known coordinates through the ordinary fact store. The AST addition is the user-approved `obj`/`line_file` payload and release enum branch. Env/Runtime state and transaction contracts are unchanged.

Before, this command was parser-rejected:

```litex
# let t=(1,2)
# release tuple def t
```

Now, the [collected tracer](../../release_and_expand/release_tuple_def.lit) checks:

```litex
let t=(1,2)
release tuple def t
t $in finite_seq(union({1},{2}),2)
t(1)=1
t(2)=2
```

The command first checks the full domain, all existing `fn_set_member` return premises, membership WD and all coordinates. It then publishes the package. Literal values/direct stored aliases use singleton unions; when no literal value is known, checked Cartesian members use factor unions and coordinate bounds. It also handles `()`, `tuple(a)`, repeated and heterogeneous values. Singletons retain the readable spelling `tuple(a)`; the former `(a)` output reparsed as a scalar. No size, image, dimension, trust, new storage owner or automatic alias/body search was added.

The nearest rejected boundary is executable in [the negative fixtures](../../../test_statements/negative/release_tuple_def_stmt):

```text
have fn z(i1 N+) R=0
release tuple def z                         # rejects; stores nothing
z $in finite_seq(R,2)                      # rejects
z $in fn(k closed_range(1,2)) R             # rejects
```

The command requires a known value or Cartesian contract; it does not discover arbitrary function definitions or follow transitive alias chains. Native controls check wrong lengths, out-of-domain/scalar coordinates, invalid WD, failed enclosing claims and sketch discard. Ordinary subsequent member checks resolve published FactIds and preserve source locations. Normal/Detailed, ten languages, LaTeX, readable source roundtrip and read-only graph projection are covered.

| Gate | Result |
| --- | --- |
| `target/release/litex -lang en -strict -f examples/stmt_nodes/release_and_expand/release_tuple_def.lit` | exit 0; all 20 statements; singleton output preserved |
| Existing strict `release_cart_def.lit` | exit 0; all 13 statements |
| Six native feature regressions | all pass |
| Current Stmt manifest | 52 leaves; 391 checks; all pass |
| README/docs Litex fence runner | 469 blocks; all pass |
| Typed graph visitor and CLI graph | current visitor check passes; checked `fn_set_member` provenance retained |
| Full Rust all-target gate | 1178 library tests pass, 3 fail; all 21 integration tests pass |
| Isolated copy without this feature | 1172 library tests pass, the same 3 fail |

The full Rust gate remains red for these independently reproduced failures; they were not repaired or hidden by changing expectations:

- Builtin theorem catalogue: `BuiltinTheoremId::from_name("named_enumeration_callbacks")` fails because this helper file is in the directory whose collector expects only theorem names.
- Compact-subcover specialization: the existing goal uses `family_union(fn_range(fn(index J) open_sets {cover(index)}))`, while the candidate retains `family_union(fn_range(\restricted<Index, open_sets, cover, J>))`; the current matcher does not establish that bridge.
- Rule prose audit: existing `less_equal.rs` English message `x in R: -1<=sign(x)` fails the localized-prose requirement.

The isolated control retains unrelated workspace changes and removes only the feature's previously clean producer/consumer paths, with a regenerated visitor. Geo, textbook migration and external Lean acceptance were outside this task. Historical `run_all`/`run_examples` filters have no current corpus collectors; the actual Cargo targets and Stmt manifest were used.

Exact gates, input hashes, native test names, session observations and the final Normal tracer envelope are in the [machine receipt](release_tuple_def_2026-10-08.json). Draft transcripts and the isolation manifest remain under `tmp/2026-10-08/tuple-def-bridge/`.
