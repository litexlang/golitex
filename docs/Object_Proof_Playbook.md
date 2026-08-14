# Object Proof Playbook

This playbook starts where the
[Goal-Shape Routing Table](cheatsheet.md#goal-shape-routing-table) stops. The
routing table chooses a proof action for the next fact. This page chooses the
object interface that must exist before that action can work.

The central rule is construction before consumption:

1. identify the exact carrier required by the next function, fold, field, or
   theorem;
2. construct a value in that carrier;
3. keep one representation equality back to the source expression;
4. establish the domain or well-definedness facts at the phase that needs
   them; and
5. apply the mathematical consumer only after those boundaries are explicit.

An equality may transport a fact without retyping an object. A proof that an
integer expression is nonnegative does not retroactively make its original
declaration `N`-valued, and equality to a finite set does not automatically
make a function's domain a `finite_set`. Use the narrowest typed alias that the
consumer actually requires.

## Quick Selection Table

| Downstream use | Construct first | Keep explicit | Do not substitute |
|---|---|---|---|
| A partial operation or refined numeric argument | A value in the exact numeric carrier | Domain, sign, nonzero, or endpoint facts | A broader value plus a later proposition that it happens to fit |
| Later code writes `F(x)` and then tests membership | A `have fn` returning the exact set carrier | The set-builder base and introduction boundary | A membership `prop` standing in for the set-valued object |
| A range cardinality, sum, product, or fold | Exact typed endpoints, iterand, operation, and seed | Endpoint order and the one fold equation used next | A compound endpoint that only propositionally has the right type |
| Later code projects and applies a record field | A typed struct/dependent-record value | Field projection before application | One opaque nested expression such as `record.entries(k)(j)` |
| A recursive value is evaluated or used inductively | A callable with a carrier-preserving recursive argument | One stored equation and the normalized inner index | Deep normalization through several recursive or wrapper layers |

## 1. Refined Numeric Values And Partial Operations

Downstream-use sentence: later code must pass a value to a consumer whose
domain is narrower than the expression's ordinary arithmetic carrier.

Use this sequence:

1. Declare the source expression in its natural carrier.
2. Prove the required domain facts propositionally.
3. Introduce a second alias in the exact refined carrier when a later consumer
   needs typed data rather than only a fact.
4. Keep the representation equality between the two aliases.
5. Construct aggregate endpoints in the exact binder carrier used by the
   aggregate interface.

The nearest rejected shape from the row-cardinality journal was
`have remainder N = q * x % p`. Modulo produced an integer object at
declaration time; Euclidean remainder bounds became available only afterward.
The accepted route kept `remainder Z`, unfolded Euclidean division, proved the
remainder bounds, selected `quotient_N N`, and finally used `lower N` and
`upper N` for symbolic range cardinality.

A second independent boundary appeared in the canonical Legendre sign-product
theorem. A header with `h N` made `finite_set_product(1...h, eps)` ill-defined
before the premises could prove `h >= 1`. The public interface correctly uses
`h N+`, because every intended caller and the product itself require a
nonempty positive range.

Current checked probes:

- [`finite_set_cardinality_builtin_rules.lit`](../examples/02_builtin_math/finite_set_cardinality_builtin_rules.lit)
  shows that the symbolic range-cardinality surface takes exact `N` endpoints
  plus their order.
- [`requested_numeric_builtin_rules.lit`](../examples/02_builtin_math/requested_numeric_builtin_rules.lit)
  shows a recursive call whose predecessor remains in the declared natural or
  positive-natural carrier.

Boundary: never infer a carrier-changing conversion from equality alone. In
particular, do not silently narrow `Z` to `N` or `N+`, and do not use a proof
body to repair an ill-defined theorem header.

Evidence journals:

- `scripts/number_theory_for_beginners/proof_journals/section12-reciprocity-row-cardinality-2026-8-11.json`, block B002.
- `scripts/number_theory_for_beginners/proof_journals/section12-legendre-gauss-product-2026-8-11.json`.
- `scripts/Concrete-Mathematics-A-Foundation-For-Computer-Science/experiments/chapter03_half_split_317_318.json`, block B002.

## 2. Set-Valued Constructions

Downstream-use sentence: later code applies a named construction to obtain a
set, passes that set to another interface, or takes its cardinality.

Use `have fn` for the construction. Its return carrier should be the exact
ambient power set required downstream. Build the set builder directly over
that ambient carrier, even when a mathematically equivalent narrower subset
is already available. Keep the predicate used inside the builder as a `prop`
only when it is independently meaningful; the predicate does not replace the
set-valued function.

The nearest rejected row-family shape built a set builder over the already
defined above-region while declaring a value in the rectangle's power set.
Well-definedness did not lift the narrower builder automatically. The accepted
definition builds directly over `cart(1...h, 1...k)` and keeps the inequality
and fixed-coordinate filters in the body.

LADR Result 2.43 supplies an independent carrier boundary. Given
`A : power_set(W)` and `W : power_set(VSet)`, the ambient pair-sum constructor
still required an explicit `A $in power_set(VSet)` premise. The accepted proof
then used long-form set extensionality and kept one operation-representation
equation in each membership direction.

Current checked probes:

- [`prechecked_goal_well_definedness.lit`](../examples/01_proof_patterns/prechecked_goal_well_definedness.lit)
  defines a `have fn` returning an exact power-set carrier and immediately
  consumes the resulting set in a proposition.
- [`gcd_from_finite_divisors.lit`](../examples/04_case_studies/gcd_from_finite_divisors.lit)
  constructs membership in a named set builder through the explicit
  `set_builder_member` interface before selecting its maximum.

Boundary: set-builder elimination is directional. Known membership exposes the
base carrier and filters; constructing membership from those facts uses the
explicit builtin theorem. Do not expect equality between set-valued functions
to transport generated binder metadata through every higher-order consumer.

Evidence journals:

- `scripts/number_theory_for_beginners/proof_journals/section12-reciprocity-row-sum-2026-8-11.json`, blocks R001--R002.
- `scripts/linear_algebra_done_right2/experience/proof_journals/2026-8-11-chapter2c-result243-sum-transport.json`.

## 3. Finite Ranges, Cardinalities, Sums, Products, And Folds

Downstream-use sentence: later code consumes a finite index domain and needs
its endpoints, enumeration, operation laws, or cardinality in an exact form.

Separate four obligations:

1. the index carrier and endpoint order;
2. the iterand's return carrier;
3. the aggregate's operation and seed laws; and
4. the equality or reindexing theorem used by the next calculation.

For `range(lower, upper)`, give `lower` and `upper` exact `N` aliases when the
generic cardinality interface has `N` binders. For an ordered `reduce`, preserve
index order; a bijection is not enough. For `finite_set_reduce`, supply an
associative and commutative operation because display order is not finite-set
semantics.

The row-cardinality journal first tried compound and `N+` upper endpoints.
Those forms did not match the generic cardinality surface. Exact `N` aliases
and an explicit `lower <= upper` bridge exposed the accepted rule. Concrete
Mathematics supplies an independent fold pattern: recursive or finite-sum
values are unfolded one stored endpoint equation at a time, with atomic
iterand values materialized before rewriting an enclosing aggregate.

Current checked probes:

- [`reduce_builtin_rules.lit`](../examples/02_builtin_math/reduce_builtin_rules.lit)
  distinguishes ordered interval reduction from associative-commutative
  finite-set reduction and records their reindexing boundaries.
- [`finite_set_product_builtin_rules.lit`](../examples/02_builtin_math/finite_set_product_builtin_rules.lit)
  shows pointwise multiplication and bijective reindexing of a finite product.

Boundary: an aggregate equality is not unrestricted rewriting under a fold.
Keep the exact endpoint or pointwise interface required by the aggregate, and
do not infer an order-sensitive fold equality from an arbitrary permutation.

Evidence journals:

- `scripts/number_theory_for_beginners/proof_journals/section12-reciprocity-row-cardinality-2026-8-11.json`, block B002.
- `scripts/Concrete-Mathematics-A-Foundation-For-Computer-Science/experiments/builtin_migration_chapter01.json`, blocks CM-BUILTIN-C1-B004--B007.

## 4. Dependent Records, FiniteList Values, Tuples, And Coordinates

Downstream-use sentence: later code projects a dependent field, applies that
field as a function, or proves equality of tuple-backed records.

Project inside-out:

1. bind the whole object in its exact struct or dependent-record carrier;
2. expose the field value, such as `columns.entries(k) = column_function`;
3. apply the projected value, such as
   `columns.entries(k)(j) = column_function(j)`;
4. prove field or coordinate equality; and
5. reconstruct opaque tuple-backed objects with
   `tuple_equal_from_coordinates` only after all required coordinates are
   explicit.

The nearest rejected row-cardinality proof called
`tuple_equal_from_coordinates` after only coordinate equalities and later even
after explicit Cartesian memberships. The reserved interface still lacked the
required tuple evidence. The accepted narrower route used the reconstruction
facts already supplied by Cartesian membership,
`point = (point[1], point[2])`, then closed the pair equality structurally.

The LADR homogeneous-system journal independently found that
`columns.entries(k)(j)` had to be split into field projection and ordinary
application. The route was revalidated against the current runtime on
2026-08-11: `matrix_columns` is deterministic template data, and
`matrix_column_combination_reconstruction` first proves one local universal
trace projection, then applies the projected entry function at the required
coordinate. This is a checked source-local interface, not evidence for a
global dependent-field congruence rule.

Current checked probes:

- [`generic_cart_member_coordinates.lit`](../examples/_internal/regression/generic_cart_member_coordinates.lit)
  reconstructs a tuple from checked coordinates and keeps explicit theorem
  calls at the constructor boundary.
- The current
  `scripts/linear_algebra_done_right/textbook/chap1a.lit` theorem
  `finite_list_extensionality` projects the two record fields, proves function
  equality for `entries`, reconstructs each opaque record, and leaves equality
  of explicit tuple literals to structural verification.
- The current
  `scripts/linear_algebra_done_right/textbook/chap3b.lit` definitions
  `matrix_columns` and `matrix_column_combination_reconstruction` construct the
  dependent list of column functions and check the projection/application
  chain in its real downstream consumer.

Boundary: do not add a tuple theorem call for two explicit same-arity tuple
literals after their coordinates are known. Conversely, do not expect a
dependent field application to normalize through an opaque wrapper or
function-returned record in one step.

Evidence journals:

- `scripts/number_theory_for_beginners/proof_journals/section12-reciprocity-row-cardinality-2026-8-11.json`, block B001.
- `scripts/linear_algebra_done_right/experience/proof_journals/2026-8-1-builtin-rule-migration-chap1a.json`, block B009.
- `scripts/linear_algebra_done_right/experience/proof_journals/chap3b-homogeneous-system-nonzero-solution.json`.
- `scripts/linear_algebra_done_right/experience/proof_journals/2026-8-11-chap3b-dependent-matrix-columns-revalidation.json`.

## 5. Recursive Callables And Shifted Indices

Downstream-use sentence: later code evaluates a recursive callable, applies an
induction hypothesis, or rewrites a recursive value inside another expression.

Use one stored equation at a time:

1. prove the recursive argument belongs to the callable's domain;
2. normalize a shifted inner index such as `(m + 1) - 1 = m`;
3. expose the exact base or step equation;
4. materialize the atomic recursive value; and
5. only then rewrite the surrounding multiplication, sum, function call, or
   fold.

The nearest rejected shifted-Hanoi shape tried to rewrite
`hanoi_moves(n - 1) + 1` directly inside an outer multiplication using the
definition of `shifted_hanoi_moves`. The inner definition equation was not
introduced through that compound context. The journal localized this exact
remaining interface debt instead of publishing more wrapper theorems.

The same workspace provides independent positive evidence in its Hanoi closed
form: the induction first establishes `(m + 1) - 1 = m`, then uses the stored
recurrence and the induction value in a single calculation. Its half-split
experiment similarly constructs `floor(n/2)` and `ceil(n/2)` in `N+` and proves
strict decrease before using them as recursive arguments.

Current checked probe:

- [`requested_numeric_builtin_rules.lit`](../examples/02_builtin_math/requested_numeric_builtin_rules.lit)
  defines natural and positive-natural predecessor recursions, with the
  domain-preserving predecessor facts visible before each recursive call.

Boundary: callability, stored equations, and executability by another checked
definition are separate capabilities. A trusted or prefix-loaded callable may
support propositions and rewriting without being a valid executable dependency
inside a new definition body.

Evidence journals:

- `scripts/Concrete-Mathematics-A-Foundation-For-Computer-Science/experiments/builtin_migration_chapter01.json`, blocks CM-BUILTIN-C1-B005--B007.
- `scripts/Concrete-Mathematics-A-Foundation-For-Computer-Science/experiments/chapter03_half_split_317_318.json`, block B002.

## Recurring Proof Bridge Retrieval Index

Retrieve a bridge only after the goal has the listed shape. The two evidence
columns deliberately point to independent source items; they are retrieval
evidence, not permission to generalize the bridge into a builtin.

| Goal shape | Retrieve this bridge | Evidence A | Evidence B |
|---|---|---|---|
| A value is known to lie in a small half-open range and the target classifies all possible equalities | Run `by enumerate range` once, then split the generated flat alternatives with `by cases`; keep substituted arithmetic atomic in each branch | [`bounded_range_classification.json`](../tests/proof_journals/bounded_range_classification.json), B001 | [`mathd_numbertheory_22_native_range_2026_08_11.json`](../scripts/litex-minif2f/proof_journals/scripts__litex-minif2f__finished__mathd_numbertheory_22_native_range_2026_08_11.json), B001--B002 |
| A recursive object is needed at one concrete base or successor argument | Introduce exactly the base or step equation consumed by the next line; do not unfold the whole recursion through an outer expression | [`builtin_migration_chapter01.json`](../scripts/Concrete-Mathematics-A-Foundation-For-Computer-Science/experiments/builtin_migration_chapter01.json), CM-BUILTIN-C1-B005--B007 | [`finite__range_sum_2026_08_04.json`](../scripts/litex-minif2f/proof_journals/scripts__litex-minif2f__cite__finite__range_sum_2026_08_04.json), B001--B002 |
| A recursive call contains `(n + 1) - 1`, `n - 1`, or another shifted inner index | Prove the shifted-index equality and its carrier before rewriting the enclosing recursive call | [`finite__range_sum_2026_08_04.json`](../scripts/litex-minif2f/proof_journals/scripts__litex-minif2f__cite__finite__range_sum_2026_08_04.json), B002 | [`builtin_migration_chapter01.json`](../scripts/Concrete-Mathematics-A-Foundation-For-Computer-Science/experiments/builtin_migration_chapter01.json), CM-BUILTIN-C1-B005 and B007 |
| A known equality or inequality must rewrite under multiplication, addition, a norm square, or another outer constructor | Materialize the exact atomic inner value or scaled comparison first, then move through one preserved outer context at a time | [`chapter02_proof_liveness_2026-8-6.json`](../scripts/mathematics_in_litex/experiments/chapter02_proof_liveness_2026-8-6.json), C02-LIVE-006--C02-LIVE-008 | [`chapter04_complex_triangle_inequality_2026_8_11.json`](../scripts/Analysis2/proof_journals/chapter04_complex_triangle_inequality_2026_8_11.json), B001-A5--B001-A8 |
| An expression is propositionally in a refined carrier, but the next declaration requires that carrier syntactically | Keep the raw value in its declaration-time carrier, prove the refinement, then select a typed alias and record its representation equality | [`section12-reciprocity-row-cardinality-2026-8-11.json`](../scripts/number_theory_for_beginners/proof_journals/section12-reciprocity-row-cardinality-2026-8-11.json), B001--B002 | [`chapter03_half_split_317_318.json`](../scripts/Concrete-Mathematics-A-Foundation-For-Computer-Science/experiments/chapter03_half_split_317_318.json), B002 |
| Set equality needs local witnesses, preimages, or several facts in either inclusion | Use long-form `by extension:` with an explicit equality goal and two scoped inclusion claims | [`section12-reciprocity-row-cardinality-2026-8-11.json`](../scripts/number_theory_for_beginners/proof_journals/section12-reciprocity-row-cardinality-2026-8-11.json), B001--B002 | [`2026-8-11-chapter2c-result243-sum-transport.json`](../scripts/linear_algebra_done_right2/experience/proof_journals/2026-8-11-chapter2c-result243-sum-transport.json), R243-SUM-TRANSPORT-A1--A2 |
| A function is stored in a dependent record field and its value is needed at an argument | Project and name the field function, establish the field equality, then apply the explicit function equality at the argument | [`chap3b-homogeneous-system-nonzero-solution.json`](../scripts/linear_algebra_done_right/experience/proof_journals/chap3b-homogeneous-system-nonzero-solution.json), `split-dependent-column-projection` through `explicit-function-equality-application-chain` | [`2026-8-1-builtin-rule-migration-chap1a.json`](../scripts/linear_algebra_done_right/experience/proof_journals/2026-8-1-builtin-rule-migration-chap1a.json), B008--B009 |
| The raw body of a named predicate is proved, but the predicate itself remains atomic unknown | Finish the body, then cross the named construction boundary explicitly with `by def`; wrap quantified uses in a `claim` | [`section2-builtin-migration.json`](../scripts/number_theory_for_beginners/proof_journals/section2-builtin-migration.json), M012 | [`chapter04_builtin_migration_2026_08_01.json`](../scripts/Analysis/proof_journals/chapter04_builtin_migration_2026_08_01.json), B004--B005 |

## Promotion And Kernel Thresholds

Keep a bridge local when it has one consumer, changes representation only
inside one proof, or has not survived a real-context deletion probe. Promote a
source-local theorem or interface when it is source-facing or has at least two
independent consumers. Consider a standard-library interface only after the
mathematical statement is stable and at least three source families use it.

Kernel work has a higher threshold. The sampled evidence currently supports
two diagnostic candidates before any semantic widening:

1. When an alias or equality fails to carry the metadata required by a
   consumer, report the exact required carrier, the expression that supplied
   the nearest known carrier, and the phase where transport was unavailable.
2. When contextual rewriting stops under an outer expression, report the
   unmatched head and nearest known equal operand. Add bounded congruence only
   after independent controls isolate a constructor-decreasing rule with a
   clear negative boundary.

The evidence does not justify general transitive carrier inference,
carrier-changing equality, arbitrary semantic rewriting under expressions, or
automatic execution of opaque callables.

## Verification

The current-source probes were rerun on 2026-08-11 with the release binary.
Each of the seven linked example files passed
`target/release/litex -compact -isolated -runner -f <file>` with exit code zero
and top-level `ok: true`. The current FiniteList implementation passed
`target/release/litex -compact -runner -f scripts/linear_algebra_done_right/textbook/chap1a.lit`
with the same result. The current `chap3b.lit` passed a no-injection,
source-order persistent replay of all 59 blocks; the materialized
`matrix_column_combination_reconstruction` block took 17.312 seconds. It also
passed the clean whole-file runner with top-level `ok: true`.

The broader executable documentation gate
`cargo test --release run_examples -- --nocapture` passed all 429 selected
example and Markdown runs. This gate includes every root-repository example
linked above. It does not cover the nested `scripts/linear_algebra_done_right`
repository; the separate `chap1a.lit` file gate is the evidence for that
current source, and the separate `chap3b.lit` session and file gates are the
evidence for the dependent matrix-column route.

## Authoring Checklist

Before keeping an object bridge, verify all of the following:

- The ordinary mathematical object and its downstream use are stated.
- The chosen Litex form is `have`, `have fn`, `prop`, `struct`, `template`, or
  `thm` for a semantic reason, not as a verifier workaround.
- The declaration uses the exact carrier required by its first real consumer.
- A nearest rejected shape is preserved in a proof journal or acceptance note.
- At least one current executable probe checks the positive route.
- A boundary states which carrier conversion, contextual rewrite, or
  higher-order transport is deliberately not inferred.
- Proof-only aliases and adapters remain lexical unless two independent
  consumers justify promotion.
