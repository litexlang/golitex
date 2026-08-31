# Registered Example Compiler/Kernel Matrix Baseline

Recorded: 2026-08-31 09:13–09:17 CST  
Classification: partial; Lean dependency changed during the run

## Command

```sh
python3 lean/coverage/kernel_check_examples.py \
  --output-dir tmp/2026-08-30/one-week-tolean-day1/all-generated --jobs 4
```

The command exited `1`. It compiled into `tmp/`; no checked-in `.lean` file
was overwritten. The release compiler SHA-256 was
`822fe2b7bd2036cc0c908c7dcde4d042a7be777c0cd54afdf271b6545c55622a`.

## Stable evidence from the run

- Registered source/pair rows: **69**.
- Direct compiler successes: **64**; direct compiler failures: **5**.
- Generated output exactly matching the checked-in pair: **16**. This hash
  comparison does not depend on the Lean build cache.
- The five compiler failures were Examples 12, 23, 24, 26, and 57. They are
  the same named-function carrier, multilayer WD carrier, anonymous-function
  WD scope, aggregate WD scope, and known-forall exact-parameter boundaries
  found by the H3 integration audit.

## Kernel evidence and interruption boundary

Before the shared `Litex/Core.olean` disappeared, 13 newly generated modules
and 17 checked-in modules passed real Lean. Two newly generated modules
reached real Lean and were rejected for non-infrastructure reasons:

1. Example 10 emits `self_exists (3 : ℂ)` although `self_exists` now requires
   an argument in `Litex.R.Carrier` (`10_ExistentialWitness.lean:97:46`).
2. Example 14 emits a direct set-builder carrier witness whose proof has the
   wrong simplified type (`14_SetBuilderAndChoice.lean:22:23`).

From Example 25 onward, many rows instead fail at import line 2 because
`lean/.lake/build/lib/lean/Litex/Core.olean` no longer exists. Those rows are
`infrastructure_failure`, not semantic kernel rejections, and the raw totals
must not be used as coverage percentages.

The dependency-changed follow-up `lake build` exits `1`, first at
`Litex/Core.lean:26:35`, then lines 66–67, while elaborating the newly added
`NumericValue` declaration. This active user-owned Core change blocks a stable
69-pair kernel census. The matrix runner has since been upgraded to schema 2:
it records kernel rejection separately from missing-object infrastructure,
and records the Lean source fingerprint before and after every run.

## Next gate

Do not retry the full matrix until `lake build` succeeds after a real Core
dependency change. Then rerun the exact command above and require:

- no dependency fingerprint change during the run;
- `core_olean_present_after_run: true`;
- all 69 rows classified explicitly as compiler pass/fail, generated kernel
  pass/reject, checked-in kernel pass/reject, and drift match/mismatch.

## Second run: Lean-stable, compiler changed

Recorded: 2026-08-31 09:40–09:48 CST

After `lake build` returned to green, schema 2 reran the matrix. Its Lean
dependency fingerprint was identical before and after, both olean-precondition
lists were empty, `Core.olean` remained present, and there were zero
infrastructure failures. It found:

- direct compiler: 64 pass, 5 fail;
- generated Lean: 57 pass, 7 kernel reject, 5 not run after compiler failure;
- checked-in Lean: 67 pass, 2 kernel reject;
- generated output matching checked-in: 17 of 69.

The five compiler failures are Examples 12, 23, 24, 26, and 57. The seven
generated kernel rejects are Examples 8, 10, 14, 36, 62, 68, and 69. The two
checked-in kernel rejects are Examples 10 and 69.

However, `target/release/stmt_result_to_lean_compiler` was rebuilt at 09:47:29
while the matrix was still running; its final SHA-256 is
`16858dc41c675da58c13dfd92200eb5b6af8ac9458dce7f3c8d877ee67dc6282`.
Therefore the named failures are valid discoveries, but these totals are not
yet a frozen single-binary coverage percentage.

The runner now additionally fingerprints the compiler binary and all 69
source/checked-pair inputs before and after. The next retry is accepted only
when compiler, example inputs, and Lean dependencies are all stable and both
olean-precondition lists remain empty.

## H3 hardening before the next retry

The stable-binary condition alone was insufficient: an old compiler binary
could remain unchanged while newer Rust source was unbuilt. The runner now
starts with
`cargo build --release --bin stmt_result_to_lean_compiler`, requires one Rust
fingerprint across that build, and carries the same fingerprint through the
entire matrix. Any Cargo failure, Rust-source change, compiler-binary change,
example-input change, Lean-source change, or stale/missing post-run olean makes
the command nonzero even if individual example rows pass.

The active RunOptions/pipeline/CLI refactor currently makes the prerequisite
Cargo build red, so a third full matrix is intentionally not started. This
avoids spending several minutes producing totals for a binary that cannot be
bound to current source.

At 10:14 CST active `Litex/Core.lean` work also removed `Core.olean`. The exact
matrix command exits `2` at its preflight with `missing
lean/.lake/build/lib/lean/Litex/Core.olean`; it does so before taking the Cargo
lock or writing generated modules. This is `B-H4-03 baseline_external` and is
the historical `B-H4-03 baseline_external` blocker.

At about 10:32 CST, after a real dependency change, `lake build` completed all
8,561 jobs at Lean fingerprint `43391bb4...`; the olean precondition and
forbidden-token scans were then empty. This resolves the missing-olean instance
of `B-H4-03`, but not the matrix evidence gate: Lean and Rust sources continued
changing afterward. The next matrix run still requires one stable Rust/source
fingerprint, one compiler-binary hash, one Lean fingerprint, and unchanged
example inputs from prerequisite build through the last kernel check.

At 10:50 CST the next H4 prerequisite check is blocked earlier, in active Rust
CLI/runtime work rather than Lean. `cargo check --all-targets` exits `101`;
the first exact error is `src/cli/command_dispatch.rs:8`, an unresolved import
of `messages::HELP_MESSAGE`. The same run also observes missing CLI module
exports and an unfinished `RunOptions` API migration, and its Rust fingerprint
changes during the check. The schema-3 matrix must therefore stop at its
release-build prerequisite and must not publish another 69-row total until the
active refactor compiles under one stable fingerprint.
This prerequisite blocker is `B-H3-03 baseline_external`; ownership remains
with the user's active CLI/runtime refactor.

The runner also now clears each row's old generated destination inside the
validated tmp directory immediately before compilation. This prevents a new
compiler failure from borrowing a stale module/hash from an earlier matrix.

## H4 current retry: release binding drift

Recorded: 2026-08-31 10:59–11:04 CST

The exact schema-3 matrix command reached its release compiler prerequisite
and then exited `1`: `Rust sources changed while binding the release compiler`.
It stopped before creating/clearing any row. The prior schema-2 report remains
byte-for-byte unchanged (recorded 09:48:41, SHA-256 `4207917d...`), and the
tmp matrix still has its prior 64 generated modules. This is `B-H4-04
baseline_external`, owned by the active Rust refactor; no coverage total from
this attempt exists.
