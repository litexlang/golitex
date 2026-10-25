# Verification and source map

The seven sample chapters are supported by eight complete public Litex
source files: one per branch, plus the IMO area-bound development in the
geometry chapter. All eight pass strict verification on the task's fixed
Litex 1.1.2-beta release executable. All seven standalone chapter examples
also pass strict verification. The acceptance date is 2026-10-24.

## What was checked

| Chapter | Complete checked source | Principal interface used |
| --- | --- | --- |
| Linear algebra | [Lecture](../../showcases/linear_algebra/linear_algebra.lit) | `standard_expansion`, `is_basis`, `standard_coordinates_unique` |
| Abstract algebra | [Lecture](../../showcases/abstract_algebra/abstract_algebra.lit) | `homomorphism_identity`, `homomorphism_inverse`, `kernel_is_normal`, the two trivial-kernel/injectivity implications |
| Topology | [Lecture](../../showcases/topology/topology.lit) | `is_topologically_continuous`, `continuous_composition`, the two-point identity counterexample |
| Analysis | [Sequence-limit slice](../../showcases/math_concepts_in_litex/10_real_analysis_in_nutshell/main.lit) | `constant_sequence_has_limit`, `sequence_limit_unique`, `sequence_limit_value` |
| Number theory | [Integer-equation slice](../../showcases/math_concepts_in_litex/3_number_theory/main.lit) | `is_gcd_certificate`, `six_is_gcd_certificate_for_84_and_30`, both Diophantine implications |
| Probability | [Finite probability slice](../../showcases/math_concepts_in_litex/8_probability_and_statistics_in_nutshell/main.lit) | `expectation2_affine`, squared-error decomposition, `bayes_rule` |
| Geometry | [Equilateral construction](../../showcases/math_concepts_in_litex/2_euclidean_geometry/main.lit) | `equilateral_vertex_distance_lemma`, `euclid_book1_proposition_1` |
| Geometry extension | [IMO area bound](../../examples/imo/geometry/imo_1966_p6/solution.lit) | `cyclic_quarter_nested`, `bkm_det_factor`, `problem_12` |

Each complete file was checked through its actual `-f` entry, including any
configured prefix. Acceptance requires process exit `0` and a parsed Normal
JSON envelope with `kind: run`, `run_result: success`,
`session_terminated: false`, and `termination: null`. Exit status alone is
not the acceptance criterion.

The standalone Markdown examples were extracted with the repository's
existing [documentation fence extractor](../../tests/tooling/run_docs_markdown_files.py)
and run in fresh files under the same strict policy. The 13 context-dependent
excerpts are marked as such and mapped to exact substrings of their complete
sources. They are covered by those sources' gates rather than being run with
their required definitions missing. Relative links and the geometry figure's
target are checked separately.

The [machine-readable acceptance record](../../showcases/verification_runs/2026-10-24-mathematical-sample-chapters.json)
contains binary and source SHA-256 values, exact commands, process results,
snippet hashes, excerpt locations and the link audit. It also preserves the
initial linear-algebra naming failure and the final repair evidence.

## Mathematical and checking boundaries

The chapters' selected source files contain no active user `trust`, `axiom`
or `abstract_prop` declarations. Strict mode rejects executed user assumptions
and trust; it does not remove Litex's builtin mathematics or replace its
verifier with another kernel. Strict mode itself permits abstract predicate
signatures, so their absence is a separate source audit. No Lean compilation,
Mathlib replay or independent soundness certification is included here.

The English prose gives complete mathematical arguments for the chapter
results. Exercise answers, the probability table and the alternative basis
calculation are explanatory mathematics, not extra formalization counts.
The selected interfaces retain their actual scope: a supplied Bezout
certificate, finite probability data, relational sequence convergence and
real coordinate geometry. General certificate existence, a general event
probability space and a synthetic construction foundation are outside these
interfaces.

The only mathematical-source edit is a bound-variable rename in eight
linear-algebra declarations. The newly reserved matrix name `trace` had
conflicted with a local partial-sum name. It is now `partial_sums`; the
statements and proofs are unchanged modulo that renaming. The accepted prefix
was retained in one Session, and the changed declarations and their
intervening dependencies were checked there before materialization. The
complete source then passed a fresh strict gate. No kernel, AST or
environment implementation was changed by this task.

## Rechecking the material

Build the current release from the repository root, then use the standard
file command on any source in the table:

```sh
cargo build --release
target/release/litex -lang en -strict -f showcases/linear_algebra/linear_algebra.lit
```

To recheck only this collection's standalone examples, the following Python
recipe reuses the existing fence extractor, creates isolated temporary files,
and checks both strict process success and the Normal envelope.

```python
import importlib.util
import json
import subprocess
import tempfile
from pathlib import Path

root = Path.cwd()
spec = importlib.util.spec_from_file_location(
    "docs_fences", root / "tests/tooling/run_docs_markdown_files.py"
)
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

with tempfile.TemporaryDirectory() as scratch:
    for chapter in sorted((root / "docs/mathematical_sample_chapters").glob("0*.md")):
        for line, code in runner.extract_litex_fenced_blocks(chapter.read_text()):
            candidate = Path(scratch) / "example.lit"
            candidate.write_text(code + "\n")
            process = subprocess.run(
                [str(root / "target/release/litex"), "-lang", "en", "-strict", "-f", str(candidate)],
                cwd=root, capture_output=True, text=True, check=True,
            )
            result = json.loads(process.stdout)
            assert result["kind"] == "run", (chapter, line)
            assert result["run_result"] == "success", (chapter, line, result)
            assert result["session_terminated"] is False, (chapter, line, result)
            assert result["termination"] is None, (chapter, line, result)
```

The dated result applies to the recorded binary and source fingerprints.
Later source or compiler changes require fresh checks before claiming the
same acceptance. Broader Cargo tests, other showcases, local textbooks and
release packaging were not gates for these chapter documents.

[Contents](README.md) · [Chinese reading guide](README.zh-CN.md)

