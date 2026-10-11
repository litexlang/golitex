# Coverage and assumptions

This showcase contains selected, independently checked modules. Its broader
mathematical roadmap is natural numbers → sets and maps → integers and
rationals → real numbers → sequences → series → infinite sets, followed by
continuity, differentiation and integration. The later topics describe a
direction, not verified content included here.

## Included public content

The showcase includes a natural-number induction example, map/cardinality
definitions and finite-product representation proofs. It reuses the existing
public sequence-limit module for constant convergence, uniqueness and `lim`.
It does not include the full eight-chapter manuscripts, series convergence
tests, general countability proofs, or choice principles. See
[README.md](README.md) for the actual source navigation.

## Broader local chapter development

The following is a status snapshot, not a table of public chapter files.
It records the local migration checkpoints and source assumption inventory
reviewed on 2026-10-11. The earlier full gates have their own pinned-version
scope: Chapters1–5 were checked on2026-10-07; Chapters6–8 reached matching
ordered acceptance on2026-10-10. Those results do not certify future edits or
claim that every exercise in Tao’s book has been translated.

| Chapter | Mathematical direction | Local development status and visible assumptions |
|---|---|---|
| 1 | Introduction | Migration checkpoint reached |
| 2 | Natural numbers, induction and recursion | Migration checkpoint reached; 2 abstract predicate declarations |
| 3 | Sets, maps and finite cardinality | Migration checkpoint reached; 2 direct trust sites |
| 4 | Integers and rationals | Migration checkpoint reached |
| 5 | Real numbers, completeness, roots and powers | Migration checkpoint reached; 7 direct trust sites and 2 axioms |
| 6 | Sequence limits and subsequences | Matching ordered migration gate passed; 11 direct trust sites |
| 7 | Series and rearrangements | Matching ordered migration gate passed; 23 direct trust sites |
| 8 | Infinite sets, arbitrary sums, products and choice | Matching ordered migration gate passed; 22 direct trust sites, 2 axioms and 2 abstract predicate declarations |
| 9–11 | Continuity, differentiation and integration | Earlier draft translations exist; current migration is unfinished and not included here |

AppendixA is an ordered dependency of the local Chapter8 development; it is
not part of this public module. The991 source-item count refers to the existing
local translation items in Chapters6–8, not991 completed assumption-free
proofs or exhaustive source-book coverage.

Across the eight local chapters there are65 direct trust sites;56 are in
Chapters6–8. These are explicit accepted assumptions, not discharged proof
obligations. The4 axiom declarations and4 abstract predicate declarations
above are separate categories. An abstract predicate supplies a signature,
not an automatically proved instance. The strict showcase does not import
these local chapter assumptions.

## Mathematical and verification boundaries

Litex supplies the number carriers, arithmetic, sets and function machinery.
The examples do not derive builtin real numbers from a completed Cauchy or
Dedekind construction. Strict verification rejects user trust and axioms;
it does not remove reliance on the verifier and its builtin rules.

The selected finite-product theorems use positive finite indices and the
current finite-sequence/function representation. They do not claim arbitrary
infinite-product existence, choice, or restored `is_cart/cart_dim/proj` syntax.
The local development also retains genuine nonempty-index restrictions in
some native product wrappers. A separate general product formulation covers
empty indices; that broader interface is not shipped in this showcase.

The local upper-bound choice-relation predicate does not require
single-valuedness. A checked function-graph construction does not imply
uniqueness from that predicate alone. This showcase makes no claim to have
resolved the remaining choice and well-ordering exercises.

The public sequence-limit file was already present in the repository; it is
reused, not a newly completed Chapter6 translation. Its named constant-sequence
template is a different interface from the still-trusted anonymous-function
transport statements in the local chapter. Passing this module does not
remove that chapter debt. No Lean comparison or compiler check is claimed
for this showcase.
