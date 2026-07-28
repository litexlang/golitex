# Litex Corpus Snapshot

This directory is a snapshot of the repository `docs/` and `examples/` trees for use by the `litex-proof-writer` skill. It is intended for targeted search, not full-context loading.

## Search Workflow

1. Search before guessing syntax or proof patterns:
   - `rg "keyword" references/litex-corpus/docs references/litex-corpus/examples`
2. Read only the smallest matching files or snippets.
3. Prefer runnable `.lit` examples when choosing a proof shape.
4. Prefer `docs/Manual.md` for syntax and behavior, then examples for idioms.

## Primary Entrypoints

- `docs/Manual.md` - main language and verifier reference.
- `docs/FAQ.md` - practical answers and caveats.
- `docs/Tutorial/Typical_Examples.md` - tutorial examples.
- `examples/00_first_steps/README.md` - starter examples.
- `examples/01_proof_patterns/README.md` - common proof patterns.
- `examples/02_builtin_math/README.md` - builtin mathematical behavior.
- `examples/03_objects_and_data/README.md` - objects, functions, sets, ranges, templates.
- `examples/04_structures/README.md` - structures and fields.
- `examples/05_case_studies/README.md` - larger examples.
- `examples/07_dataset_gallery/` - dataset translation examples.
- `examples/_internal/` - runnable regression, scratch, and std import examples; useful but may include rough local experiments.

## Snapshot Contents

- Markdown files: 25
- Litex files: 29
- Total files: 55

## Files

- `docs/FAQ.md`
- `docs/How_To_Contribute.md`
- `docs/Litex_vs_Lean.md`
- `docs/Manual.md`
- `docs/Setup.md`
- `docs/Tutorial/.order`
- `docs/Tutorial/How_Are_Facts_Verified.md`
- `docs/Tutorial/Typical_Examples.md`
- `docs/中文简要介绍.md`
- `examples/00_first_steps/README.md`
- `examples/01_proof_patterns/README.md`
- `examples/02_builtin_math/README.md`
- `examples/03_objects_and_data/README.md`
- `examples/04_structures/README.md`
- `examples/05_case_studies/README.md`
- `examples/06_std/README.md`
- `examples/07_dataset_gallery/README.md`
- `examples/07_dataset_gallery/analysis_one.md`
- `examples/07_dataset_gallery/gsm8k.md`
- `examples/07_dataset_gallery/high_school_book.md`
- `examples/07_dataset_gallery/math23k.md`
- `examples/07_dataset_gallery/math500.md`
- `examples/07_dataset_gallery/metamathqa.md`
- `examples/07_dataset_gallery/minif2f.md`
- `examples/07_dataset_gallery/number_theory_for_beginners.md`
- `examples/README.md`
- `examples/_internal/fixtures/runfile.lit`
- `examples/_internal/fixtures/runfile2.lit`
- `examples/_internal/regression/clear.lit`
- `examples/_internal/regression/do_nothing.lit`
- `examples/_internal/regression/enuermate.lit`
- `examples/_internal/regression/euler_phi.lit`
- `examples/_internal/regression/interesting_examples.lit`
- `examples/_internal/regression/no_duplicate_name.lit`
- `examples/_internal/regression/test_mathlib_compat.lit`
- `examples/_internal/regression/tmp_feature_checks.lit`
- `examples/_internal/regression/tmp_know_prove.lit`
- `examples/_internal/regression/tmp_parse_test.lit`
- `examples/_internal/scratch/tmp.lit`
- `examples/_internal/scratch/tmp2.lit`
- `examples/_internal/scratch/tmp3.lit`
- `examples/_internal/scratch/tmp4.lit`
- `examples/_internal/scratch/tmp_d8_isomorphism.lit`
- `examples/_internal/scratch/tmp_gsm.lit`
- `examples/_internal/scratch/tmp_increasing_enumerations.lit`
- `examples/_internal/scratch/tmp_interval_check.lit`
- `examples/_internal/scratch/todo_cauchy_converge.lit`
- `examples/_internal/std_imports/test_complex.lit`
- `examples/_internal/std_imports/test_int.lit`
- `examples/_internal/std_imports/test_nat.lit`
- `examples/_internal/std_imports/test_std_import_smoke.lit`
- `examples/_internal/std_imports/test_trigonometry.lit`
- `examples/_internal/std_imports/tmp.lit`
- `examples/_internal/tmp.lit`
- `examples/tmp.lit`
