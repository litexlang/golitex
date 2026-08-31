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
