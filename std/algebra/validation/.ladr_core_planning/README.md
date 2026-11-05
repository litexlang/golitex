# Core linear-algebra interface probes

Status: planning evidence complete, 2026-11-02. These are isolated validation
declarations, not a delivered public module. The canonical algebra export list
is unchanged. The [staged plan](../../../../experiments/std-library-development/ladr-phased-implementation-plan.md)
and [Litex design](../../../../experiments/std-library-development/ladr-litex-interface-design.md)
state the selected scope and subsequent proof work.

## Checked evidence

[check.py](check.py) combines the strict saved-source gate
(54 statements), independent imported-use gate (14 statements), and four
expected refusals followed by successful retained-context checks. The
boundary replay has 28 inputs: 14 importing statements, six prerequisite
facts and eight alternating refusal/recovery statements.

The source constructs actual representing matrices and reconstructed maps,
proves both generic round trips, declares real/complex direct-law inner-product
structures and induced norms, and constructs a real scalar-space instance.
It also checks orthogonal-complement/projection/adjoint specifications,
pointwise operator iteration and an SVD candidate relation. A typed candidate
relation is not an existence proof. General inner-product coordinate instances,
Cauchy-Schwarz, Gram-Schmidt, projection/adjoint existence, spectral theorems,
SVD existence and FTA are not established here.

The refusal controls check a matrix-of-map call without linearity evidence,
column index zero, a negative purported norm and a negative-definite purported
inner product. The out-of-range refusal specifically reports
`0 $in closed_range(1,3)` after the matrix's carrier has been established.
These refusals are verifier observations; a failed statement in the journals
does not by itself show that its mathematics is false.

## Reproduction and executable identity

From the repository root, reuse the existing executable:

```sh
LITEX_STD_PATH="$PWD/std" LITEX_CHECK_BINARY="$PWD/target/release/litex" \
  python3 std/algebra/validation/.ladr_core_planning/check.py
```

The checker executes the current release executable and verifies that its
content and the consumed source files remain unchanged during the run. It
does not load historical journals or reuse saved JSON results. These planning
probes make no release-wide claim.

Only accepted contiguous statements are materialized in main.lit and
use/main.lit. Positive replay inputs come from those files, while the four
refusal cases remain explicit in check.py. A higher-order iteration
alternative remains unproved; the recommended pointwise construction has its
zero/one value equations checked. No new trust, axiom, native rule or kernel
repair was introduced, and no LADR item or theorem family is accepted by this
planning check.
