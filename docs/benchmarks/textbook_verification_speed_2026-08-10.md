# Lean / Litex textbook verification speed, 2026-08-10

This report compares end-to-end command-line checking time for aligned textbook
slices. It separates:

- a Lean source check, where only the textbook project's own build artifacts
  are removed;
- a Lean cached no-op, where the identical command is run immediately again;
- a Litex run, which reparses and rechecks the selected exports every time;
- validity and proof-gap audits, without which the timing is not interpretable.

Dependency downloads, toolchain installation, and Mathlib cache extraction are
excluded. Dependencies remain precompiled in every measured source-check run.

## Result

Five measured repetitions were run after validation, alternating the Lean-first
and Litex-first order. Values below are wall-clock medians.

| Slice | Interpretation | Litex runner | Lean source check | Lean cached no-op | Lean source / Litex |
| --- | --- | ---: | ---: | ---: | ---: |
| MIL chapters 1–2, examples + solutions | **Primary chapter-aligned workflow** | **1.224 s** | **13.117 s** | 2.403 s | **10.72×** |
| MIL chapters 1–2, solutions only | Narrower diagnostic | 1.192 s | 9.122 s | 1.974 s | 7.65× |
| MIL chapters 1–3, examples + solutions | Operational only | 2.402 s | 19.574 s | 2.385 s | 8.15× |
| MIL chapters 1–3, solutions only | Narrower operational diagnostic | 2.415 s | 13.484 s | 2.464 s | 5.58× |
| Mechanics chapters 1–3 | Operational only | 1.603 s | 8.166 s | 0.489 s | 5.10× |
| Analysis chapters 2–7 | Operational only | 215.506 s | 122.171 s | 3.438 s | 0.57× |

The defensible MIL headline is:

> On chapters 1–2, the Litex strict release runner took 1.224 seconds. Building
> every official Lean file in those chapters—including the textbook
> examples/exercise scaffolds and the separate solution modules—took 13.117
> seconds, or 10.72 times as long. Under the narrower solutions-only Lean
> workload, the observed ratio was still 7.65×.

The full-workflow median cumulative CPU times were 1.204 seconds for Litex and
68.236 seconds for Lean, a 56.67× difference. In the solutions-only sequence
they were 1.188 and 28.765 seconds, a 24.21× difference. Lake used its default
parallel module scheduling, so wall time measures user waiting time while
cumulative CPU time exposes parallel compute consumption.

Analysis reverses the wall-clock result: the Lean source check took 122.171
seconds, while the Litex runner took 215.506 seconds, so Lean was 1.76× faster
in elapsed time. The cumulative CPU result points the other way: Lean consumed
436.745 seconds versus Litex's 215.453 seconds, or 2.03× as much CPU. This is an
operational comparison only because the Lean slice contains 988 sorry
occurrences and the Litex slice retains the trust and sketch debt audited
below.

The cached no-op is not semantically equivalent to the Litex repeat: Lean is
mostly deciding that existing artifacts are current, while Litex is rechecking
the slice. Even so, on the primary MIL 1–2 workflow the Litex recheck
(1.224 s) was faster than Lean's cached no-op (2.403 s), by 1.96×. On
Mechanics chapters 1–3, Lean's cached no-op (0.489 s) was faster than a Litex
recheck (1.603 s).

## Coverage and validity

| Slice and side | Files / lines / bytes | Explicit gaps or failures |
| --- | ---: | --- |
| MIL 1–2 Lean, all chapter files | 14 / 1,090 / 26,078 | 49 sorry occurrences in pedagogical exercise scaffolds; the 7 included solution modules are 421 lines / 10,308 bytes and contain 0 sorry |
| MIL 1–2 Litex exports | 3 / 602 / 22,678 | 0 trust, axiom, abstract_prop, or sketch; strict runner passed |
| MIL 1–3 Lean, all chapter files | 26 / 2,667 / 63,123 | 115 sorry occurrences in pedagogical exercise scaffolds; the 13 included solution modules are 1,123 lines / 26,747 bytes and contain 0 sorry |
| MIL 1–3 Litex checked exports | 4 / 1,362 / 50,607 | 1 trust |
| MIL 1–3 Litex local import | 1 / 1,106 / 51,393 | 1 trust; imported as a configured, unverified module by the successful main runner |
| Mechanics 1–3 Lean | 14 / 1,098 / 27,985 | 184 sorry occurrences |
| Mechanics 1–3 Litex | 3 / 2,736 / 91,693 | 5 sketch blocks |
| Analysis 2–7 Lean | 35 / 10,459 / 416,077 | 988 sorry occurrences |
| Analysis 2–7 Litex | 6 / 19,892 / 744,727 | 32 trust, 2 axiom, 2 abstract_prop, 84 sketch; runner passed |

The primary MIL workflow includes all official Lean files because solution
modules alone omit already-completed examples from the textbook files. This is
the most chapter-complete official Lean workload. It also has an unavoidable
measurement caveat: the textbook files retain cheap sorry placeholders for
student exercises while the separate solution modules verify the completed
versions, so some declarations are represented twice on the Lean side. The
solutions-only row exposes the effect of selecting the smaller Lean artifact
set. Neither row is a theorem-for-theorem identical encoding.

Line and byte counts expose the workload differences rather than normalizing
them away: the two languages package mathematical interfaces differently.
Two discovered blockers prevent stronger cross-book claims:

1. The MIL chapter-3 project imports the alternative chapter-2 module as a
   trusted configured import. Checking that imported module on its own fails at
   chapter02-basics-struct.lit:166, in one_add_one_eq_two.
2. The official Mechanics full Lean project at commit
   e660f42b13ddcb6d12b52ba036d6bd071a0cfb9b does not build under its pinned
   Lean 4.3.0 toolchain. Failures occur in chapter 8
   03_Composition.lean and chapter 9 02_Set_Operations.lean. The measured
   successful subset is chapters 1–3 only.

The earlier Analysis failure is repaired. Chapter 4 now proves the positive
rational numerator/denominator result by splitting on the denominator's sign,
and Chapter 8 exposes an alias-aware cofinal-partial-sum interface instead of
asking the verifier to transport a higher-order proposition through local
sequence aliases. Clean Chapter 4, Chapter 8, and full-book recursive runners
all returned top-level ok: true; the measured chapters 2–7 slice did so in
every validation and sample run.

## Environment and source pins

- Date: 2026-08-10
- Machine: Apple M2 Max, 12 cores (8 performance + 4 efficiency), 32 GB RAM
- OS: macOS 14.6.1, arm64
- Litex: release build, litex 0.9.113-beta
- MIL Lean source:
  [leanprover-community/mathematics_in_lean](https://github.com/leanprover-community/mathematics_in_lean),
  commit 6dfa2c166a410d2f0f278d327ea81ae0fa6d3c32, Lean 4.28.0
- Mechanics Lean source:
  [hrmacbeth/math2001](https://github.com/hrmacbeth/math2001),
  commit e660f42b13ddcb6d12b52ba036d6bd071a0cfb9b, Lean 4.3.0
- Analysis Lean source:
  [teorth/analysis](https://github.com/teorth/analysis),
  commit ffa7001c354ac8dbb3d8d3a6830be7d8a3d4daad, Lean 4.29.0-rc8

The checked-in project manifests supplied the dependency commits. One
reproducibility trap was found: running lake update in the current Analysis
checkout follows its unpinned Verso main branch and attempted to change the
toolchain to Lean 4.33.0-rc2. The benchmark instead used the exact dependency
commits already recorded in lake-manifest.json.

## Measurement procedure

For a Lean source-check round:

1. Work in a temporary copy-on-write checkout pinned to the source commit.
2. Remove only <temporary-checkout>/.lake/build.
3. Keep <temporary-checkout>/.lake/packages/**/.lake/build intact.
4. Run lake -q build on every selected .lean file's :olean target. The primary
   MIL cases select all files under the chosen chapter directories; the
   diagnostic cases select only their solutions subdirectories.
5. Require exit code 0.
6. Immediately rerun the identical command for the cached no-op sample.

For a Litex round:

1. Use a temporary litex.config exporting exactly the selected chapters.
2. Run the release binary with -compact -runner -r.
3. Require exit code 0 and top-level JSON ok: true.
4. For MIL chapters 1–2, additionally require -strict to pass.

The normal runner emits a detailed JSON trace. Output was redirected during
measured rounds, but constructing the trace remains part of the end-to-end CLI
time. Raw wall samples and median CPU times are in
[the accompanying JSON](textbook_verification_speed_2026-08-10.json).

## Interpretation

This experiment supports a narrow performance statement, not a universal
prover ranking. On the cleanest early-MIL slice, Litex was 7.65–10.72× faster
in wall time under the two documented official-artifact selections. Mechanics
chapters 1–3 also favored Litex operationally. Analysis chapters 2–7 favored
Lean by 1.76× in wall time while favoring Litex by 2.03× in cumulative CPU.
The Mechanics and Analysis rows are not scientific proof-complete comparisons:
their paired source states contain substantial and non-equivalent gaps.

The next useful benchmark expansion is to eliminate the MIL chapter-3
import/trust blockers and reduce the Mechanics and Analysis proof debt, then
rerun the same protocol on larger gap-free slices.
