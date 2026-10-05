# Field applications and positive powers — 2026-10-04

Task: implement the maintainer-authorized bounded repairs for FN07 and GEO03.
This is an L2 affected-family gate, not a complete release gate. The
[source-owned solution](../../../examples/test_statements/experience/problem_notes/field-preimage-and-power-2026-10-04.md)
contains exact examples, causes, repairs and rejection boundaries.

## Actual gates

| Gate | Result |
| --- | --- |
| New field/square public-runtime Rust tests | 8 / 8 |
| Declaration ownership, scope and rollback Rust tests | 23 / 23 |
| Existing power / FnRange Rust tests | 1 / 1 each |
| Builtin-entry permission Rust tests | 13 / 13 |
| Production strict-e positive/negative controls | 22 / 22 expected outcomes |
| Previous complete field typed-alias proof | 1 / 1 |
| New and existing strict-file tracers | 7 / 7 |
| Stmt manifest | 50 leaves, 378 checks, 0 mismatches, 0 gaps |
| Basic semantic manifest | 175 / 175 |

The 46 Rust tests execute through the public code/statement pipeline. New
controls cover Eval, Repl and RootExport contexts and assert that ordinary
rejections have no session error. The production controls check JSON success,
exit status and session_error together. Normal output actually contains the
inferred square's positive membership. No old negative was weakened.

## Binary and source identity

| Artifact | SHA-256 |
| --- | --- |
| Initial production CLI | `e276774a66ca5b1be538497847030e96a5ef1e12ec87750bc1fb93a39c2acc7b` |
| Repaired production CLI | `8a96a9f02e5f0b5a6571ed453873e4e46e5ad05a92a9020c8938231cb67c3dd5` |
| Frozen clone with old power rule | `9fdf48647a8e8fa4250f9dad7a75788b14865e9d00ad0d632c53c6d070a4dc98` |
| Same clone with repaired power rule | `099b9eff467b8d9316aa90fccb2870f1b0dca000cc83340c8fd8d88397b5bad4` |

Shared development changed other Rust files between the initial/repaired
production builds, and again before the affected Rust gates. These are scoped
binary/source snapshots, not one global frozen-tree acceptance. The recorded
final Rust, runner and CLI-control captures have zero source drift; individual
file/alias runs record their frozen binary and exact inputs. The repaired source files
are included in the raw archive with hashes; the exact production build/test
maps and intervening shared changes are retained.

The performance pair instead compiles in one isolated Cargo project: the full
Rust hash maps differ in exactly `positive_real_power.rs`. That clone remains
unchanged through the final timing run. The command collector records one
live-tree documentation change (`docs/Manual.md`, made by this task), which
does not enter the frozen clone or its binaries.

## Causal performance control

| Exact original diagnostic input | Old rule | Repaired rule |
| --- | --- | --- |
| AAS prefix with one determinant square | 56.470 s | 10.623 s |
| Same prefix with two determinant squares | — | 11.194 s |
| Prefix with two determinant products | — | 11.678 s |

All four executions succeed in strict mode. Timing is observational; no flaky
wall-clock assertion is added. The prefix's historical diagnostic target is
`0=0`, not the original AAS side-equality goal. Complete AAS and geo acceptance
belong to GEO01 and were not newly run here. The source proof/theorem contract
was not weakened to close this performance issue.

The first reported comparison used the clone's old binary and the repaired
production binary. Hash auditing found two additional concurrent source
differences. That attempt is preserved as `performance-mixed-source.json`
and withdrawn as a one-file causal comparison. The final pair above uses the
same clone for both binaries and supersedes that measurement.

The final collector and its inner script initially used the same JSON output
filename. The collector envelope is preserved; per-case codes, raw JSON,
binary hashes and times rounded to three decimals are reconstructed from
their preserved files/stdout in `performance-paired-results.json`. The archived
reproducer now writes separate filenames. No additional timing precision or
missing result was invented.

## Preserved unsuccessful attempts

- A release build encountered concurrent recursive result-type E0072 work;
  it is preserved and the corrected shared source subsequently built. This
  task does not claim authorship of that unrelated repair.
- Test construction first put `have` inside a forall fact body, used an
  unsupported dependent FnSet parameter spelling, and tried an abstract-field
  range before establishing its callable signature. Those are invalid setups,
  not new kernel regressions. The exact original tuple-field bug inputs were
  unchanged and now pass.
- Bare creation of an abstract Ops instance lacked a nonempty-carrier proof;
  the final generic control uses a checked-signature conditional forall.
  The general real-exponent declaration also failed its existing WD; the
  preserved supported fallback test uses a symbolic natural exponent.
- Historical probe labels containing `dependent` in the final CLI batch refer
  to two independently typed arguments; no dependent-FnSet support is claimed.

Full outputs, commands, code, build snapshots and failed attempts are in the
ignored `field-preimage-and-power-2026-10-04_receipts.zip`; its checksum and CRC
verification are in the neighboring
[machine receipt](field-preimage-and-power-2026-10-04.json).

## Reproduction and remaining scope

```sh
cargo test --release --offline --lib field_function_application_tests
cargo test --release --offline --lib declaration_binding_tests
cargo test --release --offline --lib infer_positive_real_power_equal
cargo test --release --offline --lib infer_fn_range
cargo test --release --offline --lib builtin_entry_policy
litex -strict -f examples/stmt_nodes/definition/field_function_preimage.lit
litex -strict -f examples/infer/atomic/field_fn_range.lit
litex -strict -f examples/infer/atomic/field_indexed_family.lit
litex -strict -f examples/infer/equal/nonzero_real_square.lit
```

Exact commands, binary paths, runner reports and source maps are in the machine
receipt/archive. The installed CLI lacks historical compact/before/runner/try
options; current strict/e/f and JSON envelopes were used. This src tree lacks
the skill's historical crate::prelude, so tests use its actual explicit imports.

No Stmt/Obj/Fact, Env/Runtime, result schema or global permission change was
needed. REL06 source-evidence projection, independent replay, all function-head
coverage, full geo/corpus and full release gates remain outside this repair.
