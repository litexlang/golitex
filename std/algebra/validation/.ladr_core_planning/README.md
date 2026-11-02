# Core linear-algebra interface probes

Status: planning evidence complete, 2026-11-02. These are isolated validation
declarations, not a delivered public module. The canonical algebra export list
is unchanged. The [staged plan](../../../../experiments/std-library-development/ladr-phased-implementation-plan.md)
and [Litex design](../../../../experiments/std-library-development/ladr-litex-interface-design.md)
state the selected scope and subsequent proof work.

## Checked evidence

[acceptance.json](acceptance.json) combines the strict saved-source gate
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

The final saved-source/imported/boundary receipts share executable SHA-256
`c805ee5aad2d68f82e976282bf566dfcffce1413471db534eb82fa7cacf2fd77`.
The initial live authoring sessions used
`6e0642d464b17f446ed90ebbd1ba2e90437db08a266bcb6d853a6f2212196d09`;
the shared executable changed concurrently, so final coherent gates rechecked
the saved evidence on the newer executable. No executable copy or build output
was created. Receipts record the consumed source/configuration hashes.

At the closing audit, the shared executable had changed again to
`1260eee02097aec11768fdef2f6d203d2436d18cae830d297c8e9af85aa450e9`.
The receipts certify the recorded c805 executable, not that later image.
All consumed source/configuration hashes still matched, and the four exact
refusal obligations were audited. A production increment must validate its
current executable; this planning result makes no release claim.

Only accepted contiguous statements are materialized in main.lit and
use/main.lit. session.json and use/session.json preserve ordinary failures and
their repairs in the same live authoring processes. A higher-order iteration
alternative remains unproved; the recommended pointwise construction has its
zero/one value equations checked. No new trust, axiom, native rule or kernel
repair was introduced, and no LADR item or theorem family is accepted by this
planning receipt.

Both live authoring sessions were closed normally after their journals and
accepted prefixes were saved. Their aggregate histories include the recorded
failed attempts; final strict acceptance refers to the clean saved prefixes.
