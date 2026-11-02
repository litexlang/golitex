# Field-matrix interfaces and proof inventory

Status: source, saved-file, imported and refusal gates passed.
Accepted source correspondence: LADR 3.29, 3.34, 3.36 and 3.39.
The selected A-B ledger is 88/119; complete FTA remains unproved.

## Exact interfaces and reused dependencies

Reuse native `matrix(K,m,n)=fn(r closed_range(1,m),c closed_range(1,n)) K`.
Dimensions m,n are natural, including zero. K is a nonempty scalar carrier;
F is a supplied `Algebra::field::Field<K>`. Existing Field and VectorSpace
definitions, function extensionality and native R/C matrix operations are reused.

Four source Obj families have one fixed contract each:

| Interface | Result and meaning |
| --- | --- |
| `field_zero_matrix<K,F,m,n>` | A two-argument function on the complete m-by-n grid with every entry F.zero |
| `field_matrix_add<K,F,m,n>(A,B)` | Same-shaped pointwise F.add |
| `field_matrix_smul<K,F,m,n>(a,A)` | Same-shaped pointwise F.mul, with a in K |
| `field_matrix_space<K,F,m,n>` | Actual VectorSpace on exactly matrix(K,m,n), constructed after proving all axioms |

The first three declarations have literal callable signatures definitionally
equal to the native matrix carrier. Public matrix-carrier and callable-carrier
theorems preserve that equality; no scalar or shape contract is relaxed.

The 26-statement `space.lit` export contains a generic carrier conversion,
the three operations, entry and signature theorems, nonempty-matrix construction,
all eight VectorSpace laws, the actual object, field-operation interfaces,
callable result carriers, typed-result entry interfaces, and the public
`matrix_carrier_is_nonempty(K,m,n)` theorem. The latter is needed explicitly
before imported generic VectorSpace goals.

The 12-statement `native_compatibility.lit` export releases six existing
R/C field definitions and proves six whole-function equalities with native
zero_matrix, matrix_add and matrix_scale. It proves no new native rule.

No predicates, reserved BT names, parser or kernel features are added.
No native-analysis roadmap change is made. The task's entire source inventory
and proof journal remain in this std module.

## Verification and compatibility

Strict source gates accept 26 and 12 statements with the pinned task binary.
The independent consumer has 126 accepted statements. It uses the public generic
interfaces, actual real/complex 2-by-3 matrices, native function equalities,
the existing abstract zero-scalar and unique-inverse theorems, and six empty-grid
space instances. Live boundary validation rejects all five planned bad inputs
and retains the valid complex calculation after each.

Final saved-file/imported-boundary receipts pass: 38 source statements,
126 independent imported statements and five retained-context refusals.
See validation/.ladr/acceptance.json. The checker hashes the executable and
recursively consumed source modules, and records failures separately from
accepted canonical source.

The earlier matrix-alias result prototype did not make template calls
well-defined. Literal callable signatures resolved it within std, with the
same mathematical carrier. A later imported nonempty-carrier obligation was
resolved by an explicit source theorem. Some concrete native equality chains
needed explicit theorem instantiations. The journals preserve these attempts;
no verifier repair, trust, axiom or unproved assumption was used.

## Remaining dependency order

1. Existing finite coordinate spaces and basis coordinates -> basis-dependent
   representing matrices and reconstruction.
2. Entry laws and finite linear combinations -> matrix products, coordinate
   action and correspondence with map addition, scaling and composition.
3. Finite-dimensional image/kernel tools -> matrix-space dimension, rank
   correspondence, homogeneous/inhomogeneous systems and rank factorization.
4. Existing inverse/isomorphism interfaces -> matrix inverses and changes of basis.

The exact proof order depends on source probes. Native rank and determinant
retain their existing R/C domains; an arbitrary-Field fact cannot be inferred
from a native complex certificate. Complete FTA, general volume and the full
exercise corpus are not delivered here.

