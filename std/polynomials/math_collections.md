# Polynomial-function inventory

## Public source interfaces

The module imports Algebra::polynomial without changing its real_polynomials,
complex_polynomials, polynomial_value<n> or polynomial_from_coefficients<n>
objects. Its `coefficients` export provides eight source theorems plus a checked
private index publication. Below, F is R for the real-prefixed interface and
C for the complex-prefixed interface.

- real_polynomial_coefficients_unique and complex_polynomial_coefficients_unique:
  (n,m N,left finite_seq(F,n+1),right finite_seq(F,m+1),j N+)/5.
  Premises j<=n+1, j<=m+1 and equality of the two original polynomial-function
  constructors imply left(j)=right(j).
- real_polynomial_excess_coefficients_zero and complex_polynomial_excess_coefficients_zero:
  the same five arguments, with n<m and n+1<j<=m+1, imply right(j)=0.
- real_polynomial_coefficient_vector_unique and complex_polynomial_coefficient_vector_unique:
  (n N,left,right finite_seq(F,n+1))/3. Equal constructor functions imply left=right.
  Their complete input domains are already the same.
- real_polynomial_leading_bounds_unique and complex_polynomial_leading_bounds_unique:
  (n,m N,left finite_seq(F,n+1),right finite_seq(F,m+1))/4.
  Equal constructor functions and left(n+1)!=0, right(m+1)!=0 imply n=m.

No new public Obj, predicate, reserved BT name/arity, native rule, strategy,
AST, Env/Runtime, parser, verifier, compiler, Lean bridge, trust or axiom is
introduced by this coefficient export. Public names distinguish real and
complex contracts.

## Forward dependency route

Native complex modulus/sums -> an explicit leading-term bound -> nonzero
positive-real evaluation -> every coefficient of a zero representation vanishes
-> same-bound uniqueness -> finite zero padding and cross-bound comparison
-> restriction of the existing R/C polynomial functions -> these eight theorems.

The positive-real restriction is constructed explicitly; functions on R, C and
R+ are not asserted equal. For R, a C-valued coefficient copy and finite-sum
substitution expose the scalar embedding. Leading-bound uniqueness follows by
contradicting the nonzero last entry with the excess-coefficient theorem.
Same-bound vector uniqueness uses pointwise agreement and function extensionality.

## Verification

The strict coefficient source target accepts 9 statements and replays its
Algebra and ComplexSums dependencies. The independent native-polynomial
consumer accepts 37 statements. It proves complete function equality for
constant i on C and -3 on R with bounds 0 and 3, then uses the comparison APIs.
The authoring Session and clean retained-context replay both accept six
required-premise refusals and every valid continuation. Source/configuration/executable
snapshots are owned by validation/.ladr/check_coefficients.py.
The fixed executable SHA-256 is
acbc6e6d9bdb9188bf2fb57bdbac22b8981486df925a53cf1154ab2c80d6de2e.

## Delivered degree dependencies

- truncation.lit: five statements, including its private index publication.
  Real/complex full-domain truncation discards a zero tail; all-zero coefficient
  representations equal the corresponding zero function.
- finite_degree.lit: thirteen statements. has_real_polynomial_degree and
  has_complex_polynomial_degree relate an original function to a natural bound
  with a nonzero last coefficient. A largest-support index gives existence for
  every nonzero polynomial; coefficient comparison gives uniqueness, nonzeroness
  and an upper bound by every supplied representation.
- bounded_degree.lit: six theorems connect these finite degrees to the existing
  polynomial spans. A nonzero bounded polynomial has degree at most its bound;
  any polynomial of such a degree belongs to that span; the zero function
  belongs to every bound.

The 5/13/6 prefix passes strict scratch and canonical replay with ExtendedReal.
The public manifest registers these files, degree_value.lit (21 statements)
and degree.lit (33). This degree checkpoint contains 87 source statements.
The following membership export brings the current module to 94.

degree_value::PolynomialDegree is exactly union(N,{real_negative_infinity}).
For each scalar field, has_*_polynomial_finite_degree_value(p,value) packages
an actual natural degree n with value=n and the proved finite-degree relation.
is_*_polynomial_degree_value(p,value) is the disjunction of the zero-function
negative-infinity case and that finite-value relation. The helper relation
keeps a nonreal infinity marker out of natural-degree argument positions.
Source theorems prove the finite and zero cases disjoint, value uniqueness,
existence for every polynomial and unique existence. No FTA or root-count
assumption enters these definitions or proofs.

## Delivered selector Obj and degree-order predicates

- degree::real_polynomial_degree(p {q fn(x R) R:is_real_polynomial(q)})/1.
- degree::complex_polynomial_degree(p {q fn(x C) C:is_complex_polynomial(q)})/1.

The predicates in these strict domains are the existing
Algebra::polynomial::is_real_polynomial and is_complex_polynomial, written with
their ordinary Litex dollar prefixes in source. Both selectors return
degree_value::PolynomialDegree. They are defined by the independently proved
unique degree-value specification, with no formula or arbitrary coefficient
witness chosen as the result. Zero has the existing real_negative_infinity
value. For nonzero functions the result is the unique natural degree with a
nonzero last coefficient.

- real_polynomial_degree_at_most(p real-polynomial function,bound N)/2.
- complex_polynomial_degree_at_most(p complex-polynomial function,bound N)/2.

Each uses Extended::main::extended_real_le(selected_degree,bound). The proved
range helper places every valid degree value in ExtendedReal; another checked
publication places natural bounds there. This keeps the negative-infinity case
outside ordinary real comparisons. The real/complex source names have one
fixed scalar contract each and no arity/type overloading.

The selector source publishes specification/1, zero/1, domain/1,
nonzero_carrier/1, nonzero_specification/1,
agrees_with_finite_degree(p,degree N)/2,
degree_value_is_extended_real(p,value PolynomialDegree)/2 and
degree_is_extended_real(p)/1, with the corresponding real/complex prefixes.
The zero theorem assumes the supplied polynomial function equals the complete
zero function; it does not infer zero from one sampled value.

polynomial_degree_at_most_of_bounded(p,bound)/2 and
polynomial_bounded_of_degree_at_most(p,bound)/2, with their scalar prefixes,
connect the predicates in both directions to the existing bounded monomial
spans. The zero branch supplies an actual all-zero coefficient witness, and
the nonzero branch uses natural-degree uniqueness and the existing extended
order on reals. The original R->R and C->C function definitions are retained.

## Selector WD and verification

Imported callers first release obj def on the selected degree function, making
its function carrier, specification and uniqueness available. A verified
original polynomial predicate and the public degree_domain theorem establish
the exact strict input carrier. The public nonzero_carrier and extended-real
range theorems are released before claims requiring those refined carriers.
All are source proofs consumed by the shared verification mechanism; no
scenario-specific WD or native branch is added.

validation/.ladr/degree_acceptance.json records a strict 33-statement final
target, its 54 registered predecessor statements, an independent 163-statement
caller and ten retained-context refusals. The whole module snapshot, caller
configuration/source and fixed executable hashes are checked by check_degree.py.
The preceding degree-value target also passes its own 21-statement clean run.
Actual examples compute real/complex quadratic degree 2, nonzero constant degree
0 despite representation bound 3, and zero degree negative infinity. Bounded
spaces are exercised at 0, 2, 5 and 7. Refusals cover false degrees, too-small
bounds, confusing upper bounds with exact degrees, natural degree at zero and
forming a selector without the original polynomial proof. A rejected input is
not a proof that its polynomial predicate is false.

The by-cases prototype and a malformed generated namespace are preserved only
in source-owned iteration journals. The former was replaced by the unique
selector; the latter caused a hard Session stop, after which the accepted
caller prefix was saved and restored. The public source and final acceptance
contain neither the malformed call nor competing selector implementations.

No reserved BT name/arity, builtin rule, strategy, AST, Env/Runtime, kernel,
parser, compiler, Lean bridge, trust or axiom was added or changed. The three
new Obj interfaces are source definitions, not native mathematical operations.
LADR 2.11/2.12 are accepted. General root count and complete FTA remain unproved.

## Original named-set elimination

membership.lit adds seven source statements. The general theorem
transfer_membership_across_equal_sets(A,B set,x A)/3 consumes A=B and proves
x in B. The real/complex_polynomial_definition_membership(p original-polynomial
set)/1 theorems instantiate this transfer with the existing named-set definition
and publish membership in the literal predicate-refined function domain.
The matching polynomial_membership_specification/1 theorems expose the original
R->R or C->C carrier and existing polynomial predicate. Two private publications
retain the already proved function carriers.

The independent imported caller declares actual values in the original named
polynomial sets and forms degree directly after using these source bridges.
The saved-file gates and fresh retained-context replay pass 7 source / 28 imported
statements / 4 refusals. The acceptance snapshot includes all 94 registered source
statements. No new mathematical assumption, native operation, reserved name,
verifier branch or trust is introduced. The earlier direct membership-search
miss remains recorded as an authoring observation, with a working std proof route.

