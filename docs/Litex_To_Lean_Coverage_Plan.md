# Litex-to-Lean coverage plan

For the latest source audit, see [remaining compiler coverage, 2026-10-26](#remaining-compiler-coverage-2026-10-26).

Inventory totals were measured on 2026-10-23. The dated checkpoints below
record subsequent implementations and checks. Geo is outside this plan's
acceptance targets.

The [current object inventory](#current-object-inventory-2026-10-25) recounts
later native-language additions; the original denominator of 94 below is historical.

The dependent-structure checkpoint reached **40/52 statement forms and 42/94
object constructors** against the original inventory. It added ordered dependent
fields to structures with set/nonempty-set/object header parameters and atomic,
flat conjunction or chain conditions. Later additions and their checked
boundaries appear in the dated sections below.

The current compiler already checks a useful combination of elementary
algebra, inequalities, sets, formula functions and named proofs. The next goal
is to expand this combination across the language by following its existing
statement, WD, verification and inference results.

## Coverage against the initial inventory

| Layer | Inventory | Existing compiler entrypoints | Remaining work |
| --- | ---: | ---: | --- |
| Statement forms | 52 | 37 at the checked coverage checkpoint | 15 forms remain outside that checkpoint; some require an explicit assumptions/model policy |
| Object constructors | 94 | 40 | 54 constructors remain outside the checked WD construction routes |
| Standard number sets | 15 | 15 | All names represented; additional arithmetic proof routes remain |
| Atomic fact variants | 72 | 18 proposition renderers | 54 variants lack a proposition renderer, before their proof routes can be replayed |
| Explicit reserved theorem IDs | 364 | 5 Lean-checked adapters | 359 IDs remain; the four membership IDs work through both `release thm` and `by thm` |
| Automatic equality builtin result branches | 232 | 45 explicitly referenced branches | Audit and implement the remaining branches and their nested certificates |
| Automatic non-equality builtin result branches | 397 | 96 explicitly referenced branches | Audit and implement the remaining branches and their nested certificates |
| Builtin strategy result branches | 138 | 23 explicitly referenced branches | 8 equality strategies and 130 non-equality strategies must be tracked separately from builtin rules |

These columns count different things. The first two count dispatcher entrypoints;
the atomic-fact column counts statement rendering; automatic-rule columns count
static references in compiler code. A reference is not a successful Lean check.
No single percentage combines these denominators.

A static scan on 2026-10-23 supplied the inventory totals. The checked increment
includes the checked proof commands, registration declarations, min/max, sign,
floor/ceiling, integer quotient/remainder, gcd/lcm, factorial, the imaginary
unit, all signed/nonzero numeric carriers, refined products/quotients, numeric/finite-set
nonmembership, sign identities, object-definition release, finite-sequence spaces, tuple-definition release and Cartesian-definition release. Automatic-rule references were recounted after the numeric increment
against the original inventory. These are coverage checkpoints,
not a claim that every test in a changing working tree passes.

`HaveObjByExistFacts`: global
and local choices from a plain existential, including dependent division WD,
pass Lean. Plain existence also consumes a cited universal conclusion with its
recorded substitution and premises. Unique existence and unsupported nested
argument-matching certificates still reject explicitly. A dispatcher arm alone
does not complete every proof route.

Statement counting expands `Stmt`, definition, object introduction, `by`,
release, witness, register, trust, proof-block and command enums to leaf forms;
a fact assertion counts once. Object counting expands the operation families
but counts `StandardSet` once, and does not expand identifier qualification,
interval endpoint combinations, function arity or limit approach metadata.
The 15 standard sets are listed separately. Nested evidence enums inside an
automatic rule are not additional rows in the 232/397 counts.

The checked 37 statement entrypoints are fact assertions; `let`; nonempty
carrier introductions; typed equalities; `have` from existence; both `obtain` forms; `have by fn_preimage`; formula functions, case-defined functions and functions selected by unique existence;
bounded function induction; concrete predicates; named theorems; theorem
release; object-, tuple- and Cartesian-definition release; finite integer-range `expand`; `by cases`, `by contra`, `by induc`, `by def`, `by thm`; both existential
witness forms; nonempty-set witnesses; `claim`; `sketch`; and reflexive, symmetric and
transitive registration declarations; `by extension`, `by fn_extension`, `by strong_induc`, `by for` and finite-set enumeration. Each retains its existing scope/domain restrictions.

The [proof-command checkpoint](Litex_To_Lean_Proof_Commands.md) records the actual paired examples, 740 passing compiler tests, 100 Lean-checked declarations and each new adapter's domain boundaries, including finite-list membership, selected-disjunction and zero-product consumers. Later numeric checkpoints appear below.

The checked 40 object entries comprise identifiers, calls, numeric literals,
standard sets and the imaginary-unit literal; add/subtract/negate/multiply/divide/power/absolute value; square
root; min/max/sign/floor/ceil; quotient/remainder/gcd/lcm/factorial; union/intersection/set difference/power set; finite enumeration/bounded builders/closed and half-open integer ranges/finite-sequence spaces;
cartesian products/tuples; and function sets/anonymous functions/function ranges/point and set preimages/composition.
Composition construction, call expansion and fixed graph laws have separate
checked examples; complete-domain comparisons retain the boundaries below.

All 15 number sets are represented: `N`, `Z`, `Q`, `R`, `C`, `N+`, `Q+`,
`R+`, `Z-`, `Q-`, `R-`, `Z*`, `Q*`, `R*`, and `C*`. Refined carriers use
bounded separation and retain ordinary membership, sign and nonzero facts.

The explicit adapters currently checked by Lean are
`tuple_equal_from_coordinates` (theorem release, finite-coordinate boundary),
`set_builder_member`, `defined_set_member`, `fn_set_member`, and
`cart_member_from_coordinates` (release and selected invocation).
Function membership currently accepts one/two-argument formula functions,
cited functions and compositions, with alpha-equivalent or proved mutually
included complete domains. Cartesian membership uses the retained finite-function
shape; finite-source membership keeps its reviewed index-set contract. Other
source/domain evidence variants still reject explicitly. This count does not include automatic arithmetic rules.

Sources of the inventory:

- [Statement AST](../src/ast/stmt.rs), [object AST](../src/ast/obj.rs),
  [atomic facts](../src/ast/fact/atomic.rs), and [reserved theorem IDs](../src/builtin_theorem.rs).
- [Statement dispatch](../src/compile_to_lean/compile_stmt_result.rs),
  [definition dispatch](../src/compile_to_lean/compile_definition_stmt_result.rs),
  [object introduction dispatch](../src/compile_to_lean/compile_define_obj_stmt_result.rs),
  [WD construction](../src/compile_to_lean/compile_fact_stmt_result/compile_obj_well_defined_result/compile_obj_well_defined_result.rs),
  and [proposition rendering](../src/compile_to_lean/names.rs).
- [Named theorem calls](../src/compile_to_lean/compile_by_stmt_result/compile_by_thm_stmt_result.rs)
  and [theorem release](../src/compile_to_lean/compile_release_and_expand_result.rs).

The local-only inventory script records all counted names and the proposed
phase for every statement form, object constructor and reserved theorem ID.
The implementation task must also track definition unfolding, fact citations,
quantifier search routes and store/inference projections; they are not included
in the automatic-builtin counts above.

### Earlier regression checkpoint, 2026-10-23

The working-tree sweep generated and Lean-checked 98 of 102 example pairs;
406 exported declarations passed the axiom audit. Four sources rejected
during compilation: `line_membership_condition` needs an inferred function-call
constructor; `newton_residual_bound` selects a nonclosed integer-power route;
`shifted_guarded_quotient_distribution` lacks a numeric observation for an
inferred sum; `square_set_membership` lacks the visible WD producer for a power.
Their older generated files are not newly reproduced by this sweep.

The equivalence, registration and min/max pairs also have a separate check
against one copied compiler executable and the checked Core. Full Rust
regression is not green: the remaining failures include changed selected
proof routes and inferred-object evidence. A later working-tree check confirmed
that all four named sources now compile; the proof-statement work owns their
repairs. This earlier sweep is not the current whole-suite acceptance result.

### Min/max follow-up, 2026-10-23

The subsequent compiler regression passed 741 tests. The two new min/max pairs
passed strict source verification, byte-for-byte regeneration and Lean 4.31.0;
13 exported declarations passed the axiom audit. Focused controls reject changed
calculation values, swapped monotonicity premises, false fixed-argument evidence,
the wrong bound constructor, and missing or reordered real-domain evidence.
The existing min/max identity and child-reuse checks remain in that focused suite.

The formula-function and conditional-selection follow-up adds two generated
pairs and freshly checks all five min/max pairs with Lean 4.31.0. All 42 exported
declarations passed the axiom audit with only `propext`, `Classical.choice` and
`Quot.sound`. The 13 focused tests pass, including missing/reversed premise and
wrong-constructor controls. The function example is 59,248 bytes; the selection
example is 6,581 bytes.

At the min/max checkpoint the broader compiler suite had 739 passes and four failures.
All four stop in `selected_arithmetic_tests::zero_division_strategy` before
`compile_run`: the tests expect a divisor strategy that the current verifier
no longer selected. A later targeted check of the current working tree passes
all four tests; the original division source also compiles and passes Lean.

The sign increment adds [real sign](../lean/examples/real_sign/) and
[shifted direction](../lean/examples/shifted_sign_function/): exact values,
integer membership, strict-sign premises and nested function-body expansion.
Seven focused tests pass. These two pairs, the min/max function pair, the
division reproduction and the repaired line-membership pair pass Lean 4.31.0
and fresh regeneration. All 49 exported declarations audited from the four
public pairs use only the standard axioms above. The line example's private
helper was renamed from `det` to `planar_det` after `det` became a matrix builtin.
The final compiler batch passes all 750 tests.

### Floor/ceiling follow-up, 2026-10-23

Three new pairs cover [exact rounding and integer identities](../lean/examples/rounding_integers/),
[bounds and weak monotonicity](../lean/examples/rounding_bounds/), and
[formula functions with nested calls](../lean/examples/shifted_rounding_function/).
They consume the existing WD, integer-membership and argument-order results;
no Runtime or AST contract changes were needed. Negative fractions distinguish
floor and ceiling from truncation toward zero.

Seven focused tests pass, including missing/wrong domain evidence, reversed
order premises and wrong-rule controls. All three pairs and the existing shifted
sign function pass strict source verification, fresh regeneration and Lean
4.31.0. The 33 audited exported declarations use only `propext`,
`Classical.choice` and `Quot.sound`. The new files are 16,157, 7,866 and 33,920
bytes respectively. The compiler batch passes 757 tests with no failures.

### Integer quotient/remainder follow-up, 2026-10-23

The integer-division increment adds [signed values and declarations](../lean/examples/signed_integer_division/),
[decomposition and bounds](../lean/examples/quotient_remainder_decomposition/), and
[functions with fact reuse](../lean/examples/integer_division_functions/).
Both constructors require integer operands; quotient requires a positive-natural
divisor, while remainder admits any nonzero integer divisor. The gcd-modulus
WD route was added in the subsequent gcd/lcm increment below. Their native bridges
use integer Euclidean division and remainder, including negative inputs.

The increment also connects positive-natural nonempty declarations, standard
number-set inclusions, and the three original sign inference stores. Function
domains retain `N+` through the existing set-domain signature. Missing nonzero
declarations found by Lean checking were repaired at the compiler's original
inference consumer; Runtime and AST contracts remain unchanged.

All three pairs and the existing shifted-rounding function pass strict source
verification, fresh regeneration and Lean 4.31.0. Their 42 exported declarations
use only `propext`, `Classical.choice` and `Quot.sound`. New generated files are
19,671, 9,458 and 51,403 bytes respectively. Focused controls cover WD domains,
closed values, decomposition shape, argument congruence, bound premises and
missing positive-natural inference stores.
The nine integer-division tests and the new sign-store test pass; the final
compiler batch passes all 767 tests.

### Gcd/lcm follow-up, 2026-10-23

Four pairs cover [signed values](../lean/examples/gcd_lcm_values/),
[identities with guarded integer parameters](../lean/examples/gcd_lcm_identities/),
the [Euclidean step](../lean/examples/gcd_euclidean_step/), and
[functions, argument substitution and theorem reuse](../lean/examples/gcd_lcm_functions/).
Gcd requires integer operands and the original proof that at least one is
nonzero; its codomain is `N+`. Lcm requires integer operands, has codomain `N`,
and permits `lcm(0, 0) = 0`. Both retain their owned constructors and use proved
bridges to `Int.gcd` and `Int.lcm`.

The eight equality consumers cover both commutativities, both self/absolute-value
identities, both gcd/zero identities, the gcd/lcm product, and the Euclidean
step. The remainder constructor can derive a gcd divisor's nonzero proof from
that already certified object's WD. Repeated constructors remain references.
Runtime, AST and semantic-model fields are unchanged.

Ten focused tests pass, including missing/reordered WD, incomplete nonzero
guards, altered calculation certificates, wrong selected rules and missing
argument-equality evidence. Actual generated files pass Lean 4.31.0; this is a
checked gcd/lcm slice, not coverage of all divisibility or primality rules.

The final compiler regression passes all 777 tests. Four new pairs and the
existing integer-division function pair pass strict source verification, fresh
regeneration and Lean 4.31.0. All 40 audited exported declarations use only
`propext`, `Classical.choice` and `Quot.sound`. New generated sizes are 47,069,
19,557, 5,526 and 194,434 bytes respectively.

### Factorial and imaginary-unit follow-up, 2026-10-23

Seven pairs cover [exact factorials and nonzero values](../lean/examples/factorial_values/),
[recurrences](../lean/examples/factorial_identities/),
[weak/strict monotonicity](../lean/examples/factorial_order/),
the [permutation-count function](../lean/examples/factorial_function/),
[exact complex values and aliases](../lean/examples/imaginary_unit_values/),
a [complex polynomial identity](../lean/examples/complex_polynomial_identity/),
and a [quarter-turn function and its two-step composition](../lean/examples/complex_rotation/).
Each directory contains the actual source and generated Lean file.

Factorial retains its original `N` argument proof and has codomain `N+`;
its denotation is connected to `Nat.factorial`. The strict monotonicity rule
retains the smaller argument's `N+` proof: `0! = 1!` prevents an unconditional
strict rule. The predecessor route also consumes integer predecessor order and
integer-plus-nonnegative refinement evidence. Its argument normalization currently
accepts the polynomial slice; missing denominator guards are rejected.

The source imaginary unit is lowercase `i`. Its numeric leaf uses `Complex.I`
inside the existing Litex number wrapper. Exact complex calculations validate
both recorded coordinates; symbolic Complex results use a fixed coordinate
normalizer. Division still consumes the original nonzero WD. This increment
does not add conjugation, real/imaginary-part operators or further number sets.

Seventeen focused tests pass. The compiler regression passes 794 tests. All
seven pairs and the existing positive Newton-update pair pass strict source,
fresh regeneration and Lean 4.31.0. The last direct factorial-nonzero source
addition is checked separately with the same frozen compiler and Core; other
unchanged pairs reuse that batch's checks. The 37 current exported declarations
use only `propext`, `Classical.choice` and `Quot.sound`. New files range from
about 4 KB to 28 KB. Runtime, AST and semantic-model fields are unchanged.

### Signed and nonzero numeric carriers, 2026-10-23

The remaining eight sets (`Q+`, `Q-`, `Z-`, `R-`, `Q*`, `Z*`, `R*`, `C*`)
use bounded separation of the existing numeric carriers. Their declarations
retain generic host representations. Membership produces the original ordered
sign/nonzero stores, which later division WD cites by FactId.

Eight pairs cover [exact values](../lean/examples/signed_numeric_values/),
[arbitrary parameters](../lean/examples/signed_numeric_domains/),
[refinement from premises](../lean/examples/refined_numeric_membership/),
[`have` declarations](../lean/examples/signed_numeric_declarations/),
[membership inclusions](../lean/examples/signed_numeric_hierarchy/),
[formula functions](../lean/examples/signed_numeric_functions/),
[observations of all eight function codomains](../lean/examples/signed_numeric_identity_functions/),
and [direct subset statements](../lean/examples/signed_numeric_subsets/).
Functions retain the existing set-domain call representation. The selected
`StandardSetSubset` builtin now has an adapter; refinement still consumes its
original base-membership and sign/nonzero children in order.

Missing or reordered stores, changed refinement subjects, forged closed values
and mismatched subset endpoints reject. Runtime, AST and model fields are
unchanged. This covers the carriers and these proof routes; it does not add
all arithmetic closure rules on signed or nonzero sets.

Eight focused tests and 802 compiler tests pass. The eight new pairs and the
existing factorial-function and positive Newton-update pairs pass strict source,
regeneration and Lean 4.31.0. After the final subset-lambda correction, the other
nine pairs regenerated identically and reused their successful checks under the
same Core and toolchain. All 133 exported declarations were audited together;
only `propext`, `Classical.choice` and `Quot.sound` occur. New files range from
3,696 to 58,321 bytes.

### Refined arithmetic closure and nonmembership, 2026-10-23

[Products and quotients](../lean/examples/refined_products/) now retain `R+`
or `Q*` membership through the four selected closure rules. Each adapter consumes
the recorded operand memberships and reuses the original operation's WD,
including division's nonzero condition. The same evidence supports a
[nonzero rational reciprocal](../lean/examples/nonzero_rational_reciprocal/),
[positive scaling functions](../lean/examples/positive_scaling_functions/), and
a [named reciprocal-product theorem](../lean/examples/nonzero_rational_product_theorem/).
These pairs combine `have fn`, `forall`, nested calls, `thm` and `by thm`.

[Numeric nonmembership](../lean/examples/numeric_nonmembership/) covers exact
fractions and decimals, excluded signs/zero, and nonreal complex values, such as
`not 1 / 3 $in Z` and `not i $in R`. It validates the retained closed-calculation
certificate. The separate `ClosedNumericNonMembership` builtin adapter has an
actual builtin-stage fixture. [Finite nonmembership](../lean/examples/finite_nonmembership/)
replays every recorded element disequality. Membership contradiction consumes
an original member/nonmember pair for the same set and derives the recorded
disequality in either orientation.

Eleven focused tests and all 813 compiler tests pass. The six new pairs and
three existing regression pairs pass strict source verification, byte-identical
regeneration and Lean 4.31.0. All 63 exported declarations, plus the builtin
fixture's declaration, use only `propext`, `Classical.choice` and `Quot.sound`.
The six new generated files range from 7,941 to 36,199 bytes. Controls reject
changed carriers, endpoints, certificates, missing/reordered child proofs and
missing division WD. Runtime, AST and model fields are unchanged.

Range/interval and other set-operation nonmembership routes remain separate
work. This increment does not add the four reserved number-theory BT adapters.

### Sign identities and function expansion, 2026-10-23

Four existing selected builtin branches now compile: `SignOfNegation`,
`SignOfProduct`, `SignTimesAbsEqualsArg` and `AbsEqualsSignTimesArg`.
Their empty identity certificates are checked against the producer's exact
structural subjects; real-domain evidence comes from the original sign WD.
The proved semantic laws use the existing numeric embedding and `Real.sign`.

The pairs cover [products and operand permutations](../lean/examples/sign_product/),
[negation spellings](../lean/examples/sign_negation/),
[sign/magnitude reconstruction](../lean/examples/signed_magnitude/), and
[formula functions with a reusable theorem](../lean/examples/direction_magnitude_functions/).
Negation admits unary minus, literal-zero subtraction and multiplication by
the producer's syntactic minus one. Both equality orientations are supported.

The function example exposed a missing type annotation on a numeric beta proof
used as an equality-chain receiver. Numeric one/two-argument expansion now emits
its original endpoint type explicitly, as the set-domain branch already did.
The ordered arguments, definition citation and original residual are preserved.

Seven sign tests and ten function-expansion tests pass. All 820 compiler tests
pass at the final checkpoint. The four new pairs and four existing sign/function
pairs pass strict source verification, exact regeneration and Lean 4.31.0.
Final regeneration reproduces all eight pairs. The two affected function pairs
were freshly checked; six identical pairs reused their checks under the same
Core/toolchain. All 47 exported
declarations were audited together with only `propext`, `Classical.choice` and
`Quot.sound`. New generated files range from 5,349 to 29,900 bytes.
Runtime, AST and model fields are unchanged.

### Object-definition release, 2026-10-23

`release obj def` now cites the facts belonging to the exact preceding
declaration captured in its execution result. It supports `let`, arbitrary
carrier/set introductions, typed equalities, `have` from plain existence and
formula-function definitions. The compiler checks the identifier, definition,
ordered returned facts and stores, then publishes the new FactIds as references
to the original proofs. It adds no Runtime state or Lean semantic axioms.

```litex
have a R = 2
release obj def a
a + 1 = 3
```

See [values and aliases](../lean/examples/released_value_definitions/),
[a guarded reciprocal](../lean/examples/released_reciprocal_definition/),
[an existential witness](../lean/examples/released_witness_definition/), and
[local definitions](../lean/examples/released_local_definitions/).
These four pairs pass strict source verification, exact regeneration and
Lean 4.31.0. Their generated files range from 4,271 to 10,784 bytes.
Seven focused tests cover original proof references, multiple parameters,
repeated release, ordered publication, corrupted results and local scope.
The compiler regression passes 827 tests; two existing theorem-release/local
proof pairs also pass Lean. All 36 exported declarations across these six
pairs use only the audited standard axioms.

Module-qualified names, recursive/piecewise/unique-existence function releases,
replacement and trust releases remain unsupported. Finite-sequence construction,
tuple release and Cartesian release are covered by the following increments.
The existing restrictions on the introducing declarations remain in force.

### Finite-sequence spaces and calls, 2026-10-23

`finite_seq(A, n)` retains an arbitrary set `A`, an arbitrary natural-number
object `n`, and their original WD proofs. Its representation uses the existing
function-graph semantics with the exact domain `closed_range(1, n)`; length zero
gives the empty domain. Membership remains an ordinary fact.

```litex
forall A set, n N, f finite_seq(A, n), k closed_range(1, n):
    f(k) $in A
```

The source inference already records `f`'s membership in the corresponding
function set. The compiler now emits that original inferred FactId and shares
its function-set constructor. Calls consume the recorded domain and membership
evidence through the existing function-call compiler. Runtime and result shapes
are unchanged; the Core additions are definitions and proved bridge laws.

See [arbitrary carriers and lengths](../lean/examples/finite_sequence_spaces/),
[legal sequence indices](../lean/examples/finite_sequence_coordinates/), and
[a first-entry formula function](../lean/examples/finite_sequence_first/).
All three pairs pass strict source verification, exact regeneration and Lean
4.31.0; generated files are 8,295, 4,661 and 14,566 bytes. Their eleven exported
theorems use only the audited standard axioms. Focused controls reject changed
WD, inferred receivers, domains, lengths, codomains and store IDs. The source
also rejects index zero for a two-entry sequence.

The batch passes 831 compiler tests. Existing finite-domain function and
Cartesian membership examples also pass Lean; their ten exported theorems
use only standard axioms. The final executable reproduces the three new pairs
byte for byte, reusing their identical-Core Lean checks.

This adds one object constructor. Tuple-definition release follows below;
Cartesian-definition release follows below; the infinite `seq` constructor remains separate work.

### Tuple-definition release, 2026-10-24

`release tuple def` now compiles for literal tuples, aliases and objects with a
recorded Cartesian membership. The result already contains the complete finite
domain, return bounds, coordinate proofs and ordered stores; the compiler replays
these before publishing their original FactIds. No Runtime or result fields changed.

```litex
have p cart(R, Z)
release tuple def p
p $in finite_seq(union(R, Z), 2)
p(1) $in R
p(2) $in Z
```

See [pair coordinates](../lean/examples/released_tuple_coordinates/),
[empty, singleton and mixed tuples](../lean/examples/released_finite_tuples/),
[Cartesian members](../lean/examples/released_cartesian_coordinates/) and
[release inside a named theorem](../lean/examples/released_local_tuple/).
Their source and generated Lean retain the original exact domain; a tuple is
represented by its function graph, including the zero-length case.

The semantic additions prove Cartesian nonemptiness from factor witnesses,
retarget a finite function's return set using its checked return proofs, and
connect the source interval endpoints to native finite indices. The compiler
also replays the selected union-membership, union-subset and finite-coordinate
return rules. Historical coordinate constructors retain their original parameter
arguments; later declarations do not become extra arguments to them.

Eight focused tests cover replay, sixteen corrupted-result variants, publication
order, original parameter contexts and local scope. The four new pairs and three
existing finite-function/theorem pairs pass strict source verification, exact
regeneration and Lean 4.31.0. The new files are 37,983, 69,892, 22,070 and
37,855 bytes. All 51 exported theorems across the seven pairs use only
`propext`, `Classical.choice` and `Quot.sound`. Two boundary pairs retain their
checks under identical binary, Core and toolchain, with byte-identical frozen
regeneration; the other five checks are fresh. The compiler regression passes
839 tests.
Cartesian-definition release follows below. Infinite sequences and additional
finite-call WD evidence variants remain separate work.

### Cartesian-definition release, 2026-10-24

`release cart def` now consumes its original equality verification and store.
The selected `CartesianDefinition` adapter validates the complete finite-sequence
bound, length, ordered coordinates and recorded alpha match. Ordinary definition
equalities use the same adapter, in either orientation.

```litex
release cart def cart(R, Z)
cart(R, Z) = {p finite_seq(union(R, Z), 2): p(1) $in R, p(2) $in Z}
```

The Core proves that an exact finite function belongs to a Cartesian product
precisely when all its coordinates belong to their factors. The return bound
retains the source's union association. Empty products retain the space of empty
functions; they are not compiled as the empty set.

See [release and subsequent citation](../lean/examples/released_cartesian_definition/),
[empty and single-factor products](../lean/examples/empty_and_single_cartesian_products/),
[arbitrary sets and three factors](../lean/examples/generic_cartesian_definitions/),
and [a local release with a reusable theorem](../lean/examples/local_cartesian_definition/).
The last example also checks set-kind theorem arguments: their recorded `IsSet`
proofs are passed through the existing theorem-call interface. Substitution
validation now descends into finite-sequence bounds and unions. Dependent
set-builder alpha identities elaborate their two constructors before applying
reflexivity inside an equality chain.

The four pairs pass strict source and Lean 4.31.0; their generated files are
22,379, 14,859, 32,454 and 57,487 bytes at this checkpoint. Five focused tests
cover thirteen malformed-result variants, publication order, local scope and
same-result replay. Clean source checks reject missing coordinates, wrong lengths
and reversed factors. No Runtime, result, AST or semantic-model fields changed. The compiler batch
passes 844 tests. Three existing tuple/function/builder pairs also pass Lean;
all 24 canonical exported theorems across these seven pairs use only the
audited standard axioms. The alternative local-theorem output is audited too.

Independent source runs can select different existing fact references in the
local theorem. Same-result compilation is deterministic; cross-run byte identity
is not claimed for that case. The checked output and sampled alternative are
retained in the local acceptance records. Logical forms such as negated
universals were still pending at this Cartesian checkpoint; the next increment
below adds their counterexample route. Unique/negative existence remains pending.

### Negated universals from counterexamples, 2026-10-24

```litex
witness exist x R st {x != 0, 1 / x != 2} from 1
not forall x R:
    x != 0
    =>:
        1 / x = 2
```

The compiler consumes `VerifyNotForallFactSuccess.derived_exist` and
`prove_derived_exist`. It validates the original binders, exact ordered domain
prefix and the producer's CNF/DNF negation, then replays the recorded existential
WD and selected proof. The target is a negated universal over semantic objects;
operations retain their Litex denotations. Its stored counterexample receives
its original inference FactId and a proof from the negative theorem.

Checked pairs cover [a singleton counterexample](../lean/examples/not_every_element_is_one/),
[a guarded reciprocal](../lean/examples/reciprocal_counterexample/),
[multiple conclusions](../lean/examples/incompatible_universal_equalities/),
[alternatives of conjunctions](../lean/examples/alternatives_counterexample/),
and [the real line, arbitrary free objects and a local theorem](../lean/examples/real_counterexamples/).
Their generated files are 5,464–39,910 bytes and pass strict source checks,
identical fresh regeneration, and Lean 4.31.0. All 22 exported declarations
were audited with only standard axioms. Four focused tests cover eleven
corrupted result variants, publication order, same-result replay, and rejection
of a true universal's negation and division without a nonzero guard.
The compiler batch passes 848 tests. No Runtime, result, AST, Core or model
fields changed; existing checked Core/toolchain artifacts were reused.

This covers ordinary verified `not forall` facts and local proof steps whose
counterexample proof is supported by the existing plain-existence compiler.
Separate NotForall WD consumers for assumptions and contradiction goals,
unique/negative existence, and unsupported existential proof routes were
outside that increment; the negative-existence update follows below. The statement count remains 32: fact assertions are
one entrypoint, regardless of their logical form.

## Negative existence: accepted replay slice (2026-10-24)

`not exist` uses the negation of the same semantic existential as `exist`.
The compiler consumes the captured WD, reverse assumption, obtained witness,
contradiction and output store. Exact later known-existential citations preserve
binder renaming. A recorded De Morgan forall is proved from the negative
existential and published under its actual inference FactId. Its parameters
retain generic host representations; witnesses use their semantic denotations.
If the producer records `NoInfer` for a body containing disjunction, no forall
is invented.

Four new checked pairs cover [singleton exclusion](../lean/examples/no_one_in_zero_singleton/),
[contradictory equalities with a named theorem, claim and theorem call](../lean/examples/incompatible_existential_equalities/),
[guarded reciprocals](../lean/examples/nonzero_reciprocal_reflexivity/), and
[alternatives in the existential body](../lean/examples/no_self_unequal_alternative/).
They pass strict source verification, identical fresh regeneration and Lean
4.31.0; generated files are 2,162–14,099 bytes. All 18 exported declarations
use only standard axioms. Existing checked Core/toolchain artifacts were reused.

Two existing citation gaps were fixed: singleton membership now emits its
recorded equality, and `obtain` returns become visible individually in their
original order inside a proof block. Completed quantified WD can supply closed
numeric/set leaves and finite enumerations of those leaves. This does not
export dependent constructors or local truth assumptions.

Five focused tests cover eight corrupted-result variants, ordered obtain
publication, private-scope rejection, same-result replay and two invalid source
controls. The compiler batch passes 853 tests. Three existing plain-existence,
guarded-counterexample and local-witness pairs also pass Lean.

No Runtime, result, AST, Core or model fields changed. The statement-entrypoint
count stays 32/52: these are additional forms of existing statement handlers.
NotForall assumptions/contradiction formation and negative-existence search
routes other than an exact saved negative fact remain open. The next increment
below adds unique-existence witness replay.

## Unique existence: witness, reuse and obtain (2026-10-24)

`witness exist!` now consumes its retained witness checks and two-candidate
uniqueness verification. Its Lean proposition is canonical semantic existence
conjoined with pairwise semantic equality. The compiler validates both fresh
candidate copies, their dependent carriers, ordered interleaved body premises
and the original equality conclusion. It does not use native host equality as
a replacement for `Litex.Same`.

For multiple variables the checked conclusion equates complete tuples. The
stored componentwise uniqueness forall follows from the existing tuple-call
laws. `obtain` projects the existential and emits its extra recorded uniqueness
forall in order. Exact unique-fact citations, named theorems, `claim`, and
explicit `by thm` calls also compile. Source-derived function dependencies now
include multi-variable uniqueness even when the body has no written tuple.

Five pairs cover [zero](../lean/examples/unique_real_zero/),
[two real coordinates](../lean/examples/unique_real_pair/),
[a reciprocal of a generic nonzero real](../lean/examples/unique_reciprocal_value/),
[a saved theorem and claim](../lean/examples/unique_real_theorem/), and
[a universal theorem instantiated at two](../lean/examples/unique_copy_theorem/).
All pass strict source verification, identical regeneration and Lean 4.31.0;
files are 11,601–30,010 bytes. All 45 exported declarations use only standard
axioms. Six focused tests include twelve corrupted-result variants, ordered
publication, private-scope rejection, same-result replay, two invalid source
controls and a then-unsupported known-forall-search boundary, covered in the
following increment. The
compiler batch passes 859 tests. Three affected plain/negative-existence and
local-witness regressions also pass Lean.

No Runtime, result, AST, Core or model fields changed. Existing checked Core
artifacts were reused; unchanged generated files reused their kernel checks
after final-binary regeneration confirmed identical bytes. Counts remain
32/52 statement entrypoints and 33/94 object constructors: this extends the
existing witness/fact/obtain handlers.

## Automatic existential theorem applications (2026-10-24)

The shared known-forall consumer now handles `exist`, `exist!` and `not exist`.
It uses the saved citation and conclusion position, validates bound-name
alignment and outer parameter substitution, and compiles every recorded
argument-match, membership and domain proof. Runtime's final structural alpha
comparison remains the boundary; this does not add matching of arbitrarily
rewritten existential bodies. Negative existence replays under hypothetical
witnesses whose facts remain local. Unique existence retains the theorem's
uniqueness proof; its existence component can also satisfy a plain `exist`
goal, from either a saved fact or a universal conclusion.

Four pairs cover [a unique copy](../lean/examples/automatic_unique_copy/),
[a guarded reciprocal](../lean/examples/automatic_unique_reciprocal/),
[two coordinates and existence weakening](../lean/examples/automatic_unique_pair/),
and [an excluded copy](../lean/examples/automatic_excluded_copy/).
All pass strict source verification, identical regeneration and Lean 4.31.0;
generated files are 6,206–24,063 bytes. The guarded reciprocal also checks
`obtain` reusing the original constructor WD from a unique-existence result.
Five new focused tests cover the selected routes, ten corrupt-result variants,
private witness scope, publication order, deterministic replay and two rejected
source controls. The compiler suite passes 864 tests. No Runtime, result, AST,
Core or model fields changed; existing checked Core artifacts were reused.
Statement and object entrypoint counts are unchanged.

Remaining unique-existence consumers are contradiction goals and the
bijective-preimage builtin. Function selection is covered by the next increment.
Bijective preimages first need the function-property semantics and consumer;
they cannot reuse the ordinary real-line witness rule.

## Functions selected by unique existence (2026-10-24)

`have fn … by exist!` now consumes the retained source-forall proof, function-set
WD, membership/property/uniqueness stores and property WD. It constructs
`SelectedFn` and publishes the three facts in their original stage order.
Later calls reuse the property under its actual FactId. Arithmetic subobjects
in that property reuse its captured WD and numeric observation under the
original bindings and checked call arguments. Function values remain transparent
through those bindings; no Runtime search, AST shape or compiler state changed.

Four pairs cover [identity](../lean/examples/selected_identity_function/),
[a nonzero reciprocal](../lean/examples/selected_reciprocal_function/),
[two-input addition and closed evaluation](../lean/examples/selected_sum_function/),
and [identity on an arbitrary, possibly empty set](../lean/examples/selected_set_identity_function/).
They pass strict Litex and Lean 4.31.0 with warnings treated as errors;
generated files are 12,928–28,112 bytes. Replay of the same typed result is
deterministic. Independent source runs for the arbitrary-set example can choose
different evidence; both observed outputs were checked by Lean.

The consumer validates exact source/store shapes, bound-variable renaming,
carriers and free inputs. Tests also check publication order, private WD
assumptions, malformed captures, missing uniqueness and an invalid zero input.
All 869 compiler tests pass. The four new pairs export 20 Lean-checked theorems;
two existing pairs and the original callee-constructor chain also pass fresh
Lean checks. The theorem audits contain only `propext`, `Classical.choice` and
`Quot.sound`.
The only added Core law in this consumer increment identifies the numeric
observation of a numeral with that numeral; the selected-function semantic
construction was checked in the preceding increment.

This adds one statement entrypoint: 33/52 statements, with object entries still
33/94. The current declaration has one output witness and uses the existing
supported function signatures. Local selected-function declarations,
unsupported signature-WD routes, general higher-order/dependent signatures,
unique-existence contradiction goals and bijective preimages remain outside
this increment.

### Quantified contradiction and negated premises, 2026-10-24

Four new source/generated pairs cover [a negated universal proved by
contradiction](../lean/examples/contradiction_to_counterexample/),
[universal reflexivity](../lean/examples/contradiction_to_reflexivity/),
[a reciprocal under a nonzero premise](../lean/examples/contradiction_with_reciprocal_guard/),
and [a negated universal theorem premise followed by `obtain`](../lean/examples/negated_universal_premise/).
This completes the NotForall assumption/goal-formation consumers left open at
the earlier counterexample checkpoint.

The compiler consumes the original parameter introductions, ordered premise
stores and conclusion WD. It derives the recorded counterexample by De Morgan
laws and keeps its original FactId. The contradiction bridge converts between
generic host representations and canonical semantic objects; it does not infer
a numeric host type from membership. A first carrier such as `{a}` is constructed
before the quantified variable exists, so its original WD can be reused by a
later `obtain`. Hypothetical parameters, premises and body constructors remain
local.

All four pairs pass strict source verification, identical regeneration and
Lean 4.31.0 with warnings treated as errors. Generated files contain 43–128
lines and 2,407–7,953 bytes. Nine new theorems and twelve declarations from
three neighboring regression pairs passed the standard-axiom audit. All 874
compiler tests pass, including malformed captures, missing guards, false goals,
free-input capture and private-fact/WD visibility controls. Runtime, result
types and `Litex.lean` are unchanged. Counts remain 33/52 statement entrypoints
and 33/94 object entries; this expands existing logical routes.

Quantified `impossible` closing facts and top-level named NotForall goals are
outside this increment's checked boundary; the four cases close contradictions
with atomic facts. The following increment adds unique-existence goals.

### Unique existence by contradiction, 2026-10-24

`by contra` now compiles `exist!` goals. Six source/generated pairs cover
[one witness](../lean/examples/unique_singleton_by_contradiction/),
[two real coordinates](../lean/examples/unique_pair_by_contradiction/),
[a nonzero reciprocal condition](../lean/examples/unique_guarded_value_by_contradiction/),
[a reusable theorem with an arbitrary real input](../lean/examples/unique_copy_by_contradiction/),
[arbitrary set objects](../lean/examples/unique_set_copy_by_contradiction/), and
[a dependent carrier](../lean/examples/unique_dependent_pair_by_contradiction/).
In the last example, the second witness belongs to the first witness's singleton.

The reverse assumption retains the producer's exact form: every candidate
satisfying the original conditions has an alternative satisfying those
conditions, with at least one different component. Compilation checks the
fresh binder identities, dependent carriers, substituted body and ordered
disequality disjunction. A fixed classical proof constructs this assumption
from denied unique existence. Uniqueness remains equality of denotations;
multiple witnesses use the existing tuple semantics.

Finite-set substitution and the existing `obtain` constructor factory now
handle a carrier such as `{a}` after witness renaming. The factory applies the
original WD under its original parameter prefix and the returned FactIds.
It does not reopen later premises or export local witnesses.

All six pairs pass strict Litex and Lean 4.31.0 with warningAsError. Final-binary
regeneration matches their checked files exactly: 81–225 lines and
6,534–20,403 bytes. Twelve new theorems and seventeen declarations from three
neighboring pairs pass the standard-axiom audit. All 881 compiler tests pass.
The seven focused tests include absent/nonunique candidates, missing WD,
changed alternatives, free-input capture, dependent carrier substitution and
constructor publication boundaries. Runtime, result types and `Litex.lean`
are unchanged; counts remain 33/52 statements and 33/94 objects.

The following increment covers quantified closing formulas and top-level named
NotForall goals.

### Quantified closings and named counterexamples, 2026-10-24

Seven new source/generated pairs cover
[universal closings](../lean/examples/universal_contradiction_closing/),
[guarded universal closings](../lean/examples/guarded_universal_contradiction_closing/),
[negated universal closings](../lean/examples/counterexample_contradiction_closing/),
[unique existence](../lean/examples/unique_contradiction_closing/),
[unique coordinates](../lean/examples/unique_pair_contradiction_closing/),
[a named counterexample followed by `obtain`](../lean/examples/named_counterexample/),
and [reusing one local universal across object representations](../lean/examples/counterexample_after_universal_use/).

The closing consumer replays both retained verification trees in order,
validates their subjects and optional exact citations, then applies a fixed
logical elimination. Tuple uniqueness contradicts the recorded component
disequality through the existing tuple projection laws. Named NotForall goals
publish their recorded counterexample inference after the theorem is complete;
private witnesses remain private.

Local reverse-forall assumptions quantify over semantic objects. Each use
lifts the same FactId to its caller's original object representation. The
adapter uses the assumption's original WD prefix, without reopening later
facts. This avoids fixing a local hypothesis's universe at its first use.
No Runtime, result, AST, Core or model contract changed. Entry counts remain
33/52 statements and 33/94 objects: these are additional routes of existing
statement forms.

The seven new pairs and nine affected neighboring pairs pass strict Litex,
byte-identical regeneration and actual Lean 4.31.0 with warningAsError.
All 43 exported declarations have only `propext`, `Classical.choice` and
`Quot.sound` in their axiom audit; new files are 3,712–23,575 bytes.
All 887 compiler tests pass, including six focused tests for malformed closing
subjects/citations, missing formation or counterexample inference, private-scope
escape, false goals and absent guards.
Further nesting and additional theorem-selection shapes remain separate coverage
work. The bijective-preimage consumer is checked in the mapping increment below.

### Case-defined functions, 2026-10-24

`have fn … by cases` now has a checked top-level declaration and call route.

```litex
have fn reciprocal(x R) R by cases:
    case x = 0: 0
    case x != 0: 1 / x
reciprocal(2) = 1 / 2
reciprocal(0) = 0
```

Four source/generated pairs cover [absolute value](../lean/examples/piecewise_absolute_value/),
[a reciprocal extended to zero](../lean/examples/piecewise_total_reciprocal/),
[two-input maximum](../lean/examples/piecewise_larger_value/), and
[a nonzero-domain reciprocal magnitude](../lean/examples/piecewise_inverse_magnitude/).
The reciprocal pair also states its branch equation for an arbitrary nonzero real.
All four pass strict source verification and Lean 4.31.0; generated files are
14,492–34,500 bytes. Four neighboring unique-existence function pairs also pass.
The compiler suite passes 893 tests; three affected producer tests and the
algorithm-dispatch regression pass separately.

`PiecewiseFn` stores the original branch list. Its WD requires coverage,
pairwise disjointness and return membership, replayed from the declaration's
three captured checks. Its graph and call theorem use existing
`FunctionSemantics` laws; no model fields or semantic axioms were added.
The compiler exports each stored branch equation under its original FactId.
A selected unfold now retains the already-computed guard proof alongside the
case index, expanded body and residual equality. This is a local result-capture
change; Runtime/Env storage and source AST shapes are unchanged.

The checked slice uses one or two real inputs, two branches, the existing
formula bodies and optional nonzero domain conditions. The real-order coverage
rules `a < b or a >= b` and `a > b or a <= b` replay their original real-membership
certificates, including reversed branch order. Local declarations, template
instantiations, general higher-order bodies and unimplemented coverage-rule
variants remain outside this slice. Counts are now 34/52 statement entrypoints
and 33/94 object constructors. The 45/96 automatic equality/non-equality counts
above retain their earlier inventory; these two disjunction rules are a
separate result family.

Independent source runs can choose different existing fact citations. A captured
alternative for the neighboring arbitrary-set identity pair also passes Lean;
this does not imply byte-identical output across independently verified runs.
Recompiling the same typed run is deterministic.

### Mapping properties and unique preimages, 2026-10-24

The compiler now consumes `Injective`, `Surjective` and `Bijective` definition
results, their stored definition consequences, and the `BijectivePreimage`
existential builtin. For example:

```litex
forall A, B set, f fn(t A)B, y B:
    $bijective(A, B, f)
    =>:
        exist! x A st {f(x) = y}
```

Four checked pairs cover [identity](../lean/examples/identity_bijection/),
[property inference](../lean/examples/mapping_property_inference/),
[translation by one](../lean/examples/shift_bijection/), and
[unique preimages on arbitrary sets](../lean/examples/bijective_unique_preimages/).
The last pair checks both equation orientations. Translation uses explicit
cancellation and the witness `target - 1` before folding the mapping properties.
All four pass strict Litex, identical independent regeneration in this check,
and Lean 4.31.0. Their generated files are 12,736–26,757 bytes; 28 exported
theorems use only `propext`, `Classical.choice` and `Quot.sound`.

The semantic definitions use the original function's `callValue`. Bridge
lemmas preserve proof-bearing existential memberships; object parameters keep
their original host representations. The compiler replays captured WD and
requirement proofs, exports original inference IDs and consumes the exact
bijection/target-membership certificate. No result producer, source AST,
Runtime/Env state, model field or semantic axiom changed. Raw call rendering
also accepts an original visible function parameter with its checked signature.

Five new focused tests cover deterministic replay, definition/WD corruption,
preimage certificate and target corruption, witness independence, and fact
publication order. The compiler suite passes 898 tests. These are new predicate,
inference and existential-rule consumers within existing statement/Obj forms;
the 34/52 statement, 33/94 Obj and 45/96 equality/non-equality counts are unchanged.

The accepted WD route uses an exact unary callable signature. Carrier-equality
and finite-prefix signature conversions and general higher-order mapping properties
remain separate work. Range/preimage support is recorded below. Negative predicate
proof routes and equality transport of mapping-property arguments are not claimed
by this batch.

### Function ranges and preimage statements, 2026-10-24

The new statement entrypoint is `have by fn_preimage`; the new Obj constructor
is `fn_range`. At that checkpoint, coverage reached **35/52 statement forms and 34/94 object
constructors**, against the same original inventory. This does not recount the
automatic builtin branches or imply complete coverage of either new entrypoint.

Four pairs cover [a real shift](../lean/examples/shift_range_preimage/),
[a guarded reciprocal](../lean/examples/reciprocal_range_preimage/),
[a two-input sum](../lean/examples/sum_range_preimage/), and
[arbitrary set/function parameters](../lean/examples/function_range_members/).
The reciprocal includes a local preimage declaration in a named theorem.
The original known-property certificate proves calls belong to their range;
stored range membership supplies codomain membership and an existential
preimage. New names and guard/equality facts keep their actual source IDs.

The two original producers previously discarded the selected signature's
FactId. Their typed results now retain that selection, and the preimage
statement retains its renamed parameters. Detailed JSON exposes the selection
and source verification; reading capture follows the typed fields. Selection
order, search and Runtime/Env storage are unchanged. A preimage statement's
call is constructed from its signature and returned domain stores, without
inventing a VerifyObj result. Its existence proof is emitted once for reuse.

`Litex.lean` defines range independently of the selected signature and proves
its bridges from existing separation and graph laws. There are no new semantic
model fields or axioms. The source AST is unchanged.

The four source/generated pairs pass strict Litex, identical independent
regeneration and Lean 4.31.0. At that checkpoint the generated files were
8,914–54,269 bytes.
Eight focused tests cover replay, evidence corruption, publication order,
generic/guarded/two-input examples, JSON citations and two executable rejection
boundaries. The compiler regression passes 906 tests.

This checkpoint uses original anonymous-function or exact membership domain
evidence and the known-property call-in-range route. The anonymous-application
builtin and positive-input preimages were completed in the follow-up below.
Dependent input carriers, other complete-domain variants and additional range
identity rules remain separate work.

### Anonymous ranges and positive preimages, 2026-10-24

The compiler now consumes `AnonymousFnApplicationInFnRange`, including its
original function-equality certificate and certified call. Anonymous-function
alpha-equality also has a consumer: it validates the original source bodies and
binders before emitting semantic reflexivity. Raw predicates use the original
certified literal constructor, preserving its captured objects.

Positive numeric signatures represent an `R+` input as real membership and a
positivity guard. Preimage extraction now separates the guards in their original
order and proves each positive membership with `positiveReal_members`, then
exports the explicit conditions with their original FactIds. No Core, result
producer, Runtime or AST changes were needed.

New pairs cover [anonymous identity and quotient calls](../lean/examples/anonymous_function_ranges/),
[a positive identity preimage](../lean/examples/positive_range_preimage/),
[two positive preimage coordinates](../lean/examples/positive_pair_preimage/) and
[a punctured positive interval](../lean/examples/guarded_positive_preimage/),
including a local declaration in a named theorem. They pass strict Litex,
identical independent regeneration and Lean 4.31.0, with 15,252–94,532 bytes of
generated Lean. Four new tests and the updated two former rejection tests cover
these routes, corrupted equality/WD, changed carriers/guard order, deterministic
replay and a source-valid nested-capture rejection. The compiler suite passes
910 tests. Entry counts remained 35/52 statements and 34/94 objects; these are
additional proof routes and domain cases of those entries.

The nested-capture rejection at this checkpoint has since been resolved for
fixed numeric signatures; see [immediate inner application](../lean/examples/nested_function_application/)
and the captured-function checkpoint below.

### Local sketches, 2026-10-24

`sketch:` now replays every original `proof_steps` result in its captured
`local_env`. A top-level sketch becomes a private Lean theorem of `True`; a
nested sketch becomes a local proof of `True`. These scope markers have no
source FactId. All child objects and proofs are checked, and none is exported.
The original prefix still controls citations, including cached WD and outer
parameters. Unsupported or failed children reject the complete artifact.

Five source/generated pairs cover [local arithmetic and name reuse](../lean/examples/local_arithmetic_sketch/),
[nested calculations](../lean/examples/nested_arithmetic_sketch/),
[theorem parameters and citations](../lean/examples/sketch_in_named_theorem/),
[tuple coordinates](../lean/examples/local_tuple_sketch/) and
[finite-set membership](../lean/examples/local_finite_set_sketch/).
They pass strict source verification, identical independent regeneration and
Lean 4.31.0; generated files are 2,425–29,495 bytes. Three neighboring examples
also pass. Six private sketch declarations and thirteen public declarations
across the eight examples audit to `propext`, `Classical.choice` and `Quot.sound`
only. Core is unchanged; its previously checked module was reused.

Nine new compiler tests check replay, source capture, child failure, unsupported
children, future/deleted producers, nested-scope isolation and cached WD.
The earlier sketch-rejection test now checks acceptance without a public claim.
The full compiler suite passes 919 tests. No result, Runtime or AST changes
were needed. Statement coverage is **36/52** against the original inventory;
object coverage remains **34/94**. Local `have fn` declarations retain their
existing `Function/LocalDeclaration` rejection.

### Finite integer-range expansion, 2026-10-24

`expand: x $in range(a, b)` and its `closed_range` counterpart now consume the
original membership proof, ordered integer values and stored disjunction. The
compiler checks that every value and equality branch belongs to the complete
enumeration, then publishes the original FactId. The membership check's local
environment stays inside the command. Empty or more-than-1,024-value expansions
are rejected, matching the source executor.

`RangeObj` represents `[a, b)` by bounded separation over integers and carries
both endpoint WD and integer-membership proofs. The existing closed interval
keeps its inclusive upper endpoint. Both families now compile their captured
integrality, lower/upper-bound, positive-carrier and singleton-equality
inferences. Endpoint variables work for construction and bound projections;
enumeration requires exact closed integer endpoints. No Runtime, result or AST
changes, new model fields or axioms were needed.

Seven source/generated pairs cover [half-open expansion](../lean/examples/expand_half_open_integer_range/),
[closed negative intervals](../lean/examples/expand_closed_integer_range/),
[a singleton](../lean/examples/expand_singleton_integer_range/),
[calculated endpoints](../lean/examples/expand_calculated_integer_range/),
[bounds with arbitrary endpoints](../lean/examples/integer_range_bounds/),
[positive carriers and signed singletons](../lean/examples/integer_range_carriers_and_singletons/)
and [a square bound proved by cases](../lean/examples/integer_range_square_bound/).
All pass strict Litex, identical independent regeneration and Lean 4.31.0;
generated files occupy 7,290–18,873 bytes. Three neighboring sequence, sketch
and Cartesian examples also pass. Eleven new Core theorems and 25 public
declarations across the ten examples audit to `propext`, `Classical.choice` and
`Quot.sound` only.

The nine new tests cover replay, endpoint WD, complete enumeration, stored
branch order, publication scope, inferred conclusions and rejection boundaries.
The live-worktree compiler suite passes **928 tests**. Real Lean checks used a
snapshot with identical compiler sources while an unrelated reading projection
was being regenerated. Statement coverage is **37/52**, object coverage **35/94**.
Range-based `by for`/enumeration is implemented in the following increment;
multi-variable enumeration remains separate work.

### Integer-interval proof iteration, 2026-10-24

Both `by for` and `by enumerate finite_set` now accept one parameter over a
displayed list, `range(a, b)` or `closed_range(a, b)`. Interval endpoints must be
exact closed integers. The consumer validates the complete ordered assignments,
then replays each original binding, premise, proof step and returned fact. A
skipped assignment needs its recorded proof that an antecedent is false; an
empty interval closes from its contradictory membership bounds. The source's
1,024-assignment limit remains in place.

The seven interval pairs cover [four square values](../lean/examples/integer_range_square_values/),
[negative closed-interval values](../lean/examples/closed_integer_square_values/),
[division with a nonzero guard](../lean/examples/guarded_integer_range_division/),
[empty intervals](../lean/examples/empty_integer_range_enumeration/),
[a negative singleton](../lean/examples/singleton_integer_square_enumeration/),
[a local loop and named theorem call](../lean/examples/named_integer_range_enumeration/)
and [calculated endpoints](../lean/examples/calculated_integer_range_enumeration/).
An additional [nested order substitution](../lean/examples/nested_numeric_order_substitution/)
checks the recorded arithmetic-subterm rewrite used inside those loops.

Enumeration-created numeric literals retain their own native payload inside
their assignment. They do not inherit the host representation of an enclosing
negation object just because the source WD cache uses the same IR. The final
conjunction cites the emitted conclusion FactIds rather than copying their
proof terms again. Core, source AST, Runtime and result producers are unchanged.

The live CLI builds and the compiler suite passes **935 tests**, including
seven new checks for coverage, binding subjects, sibling/future citations,
literal scope, skipped premises and subterm-citation order. Eight new pairs
and four neighbors have strict-source, regeneration and Lean 4.31.0 evidence;
four unchanged Lean checks were reused after fresh byte-identical generation.
All 29 public declarations audit to `propext`, `Classical.choice` and `Quot.sound`
only. The new interval files occupy 3,892–87,048 bytes. Citing the emitted
conclusions reduces the four-square example from 78,625 to 65,622 bytes.

This extends proof routes of existing entries: counts remain **37/52 statement
forms and 35/94 object constructors**. Cartesian assignment products, dependent
enumeration domains and raw functions that construct intervals from their own
bound inputs remain outside this increment.

### Cartesian enumeration products, 2026-10-24

`by for` and `by enumerate finite_set` now compile independent combinations of
lists, `range` and `closed_range`, including several names in one parameter
group. The compiler validates every original assignment in source order (last
parameter varies fastest), the 1,024-product budget, and the binding subjects.
An empty factor closes the whole product without expanding the other factors.

Each branch replays all original parameter memberships and binding FactIds,
then its premise prefix, proof steps and conclusions. Transport composes the
recorded equalities one variable at a time. A skipped branch must retain the
proof of the exact failed guard. The source cursor now traverses parameter WD
by group, reusing the existing header visitor. Runtime, result producers, AST
and Lean Core are unchanged.

Seven pairs demonstrate [two integer ranges](../lean/examples/integer_rectangle_square_bound/),
[a range with a list](../lean/examples/mixed_finite_product_commutes/),
[shared list parameters](../lean/examples/binary_product_commutes/),
[three parameters across two groups](../lean/examples/finite_triple_product/),
[two nonzero guards](../lean/examples/nonzero_integer_pair_division/),
[an empty factor](../lean/examples/empty_integer_rectangle/), and
[a local enumeration reused as a theorem](../lean/examples/named_integer_rectangle_bound/).

The full compiler suite passes **942 tests**, including seven product tests.
All seven new pairs and four neighbors pass strict source verification,
byte-identical regeneration and Lean 4.31.0 checking. At the final checkpoint,
10 kernel checks were reused after verifying identical generated bytes, Core
and toolchain; the repaired local-theorem citation was checked afresh. All
19 public declarations audit to `propext`, `Classical.choice` and `Quot.sound`
only. New files occupy 5,687–325,634 bytes. Local citations adapt every
parameter and original membership FactId, fixing the former first-argument-only
adapter.

Dependent domains such as `forall x {0,1}, y {x}` still have an explicit compiler
rejection. The selected-strategy gap found for `x+y<=4` on `[0,3) × [1,3)`
is covered by the weak additive-shift increment below. This extends existing statement routes; it
does not change the preceding inventory baseline of **37/52 statement forms
and 35/94 object constructors**.

### Weak additive shifts and numeric bound weakening, 2026-10-24

Eight more recorded order routes compile: four weak additive shift strategies
and four numeric lower/upper-bound weakening builtins, for strict and weak
goals. The rectangular sum proof selected `AddLeftNonpositiveShiftRight` in
its zero-coordinate branches; one child selected `NumericUpperBoundWeakenLe`.
Both now replay their original evidence.

| Selected strategy | Core theorem |
| --- | --- |
| `AddRightNonnegativeShiftLeft` | `Litex.leAddOfLeOfNonneg` |
| `AddRightNonnegativeShiftRight` | `Litex.leAddOfLeOfNonnegSwap` |
| `AddLeftNonpositiveShiftLeft` | `Litex.addLeOfLeOfNonpos` |
| `AddLeftNonpositiveShiftRight` | `Litex.addLeOfLeOfNonposSwap` |

The strategy consumer validates the sum constructor, both ordered requirements,
source subjects and comparison strength. Search-child visibility follows the
recorded order. Numeric weakening resolves its exact cited `<` or `<=` fact,
checks the unchanged variable and literal integer endpoints, then applies the
existing denotation and order-transitivity laws. A strict goal requires either
a strict source bound or a strict gap between endpoints. It neither searches
for another fact nor strengthens a weak bound at the same endpoint.

Eight source/generated pairs cover [additive lower bounds](../lean/examples/weak_additive_lower_bounds/),
[additive upper bounds](../lean/examples/weak_additive_upper_bounds/),
[numeric lower bounds](../lean/examples/weaken_numeric_lower_bounds/),
[numeric upper bounds](../lean/examples/weaken_numeric_upper_bounds/),
[a rectangular sum](../lean/examples/integer_rectangle_sum_bound/),
[mixed finite domains](../lean/examples/mixed_finite_rectangle_sum_bound/),
[three binary integers](../lean/examples/binary_cube_sum_bound/) and
[a local enumeration with theorem reuse](../lean/examples/named_integer_rectangle_sum/).

The compiler suite passes **950 tests**, including eight new tests for the
selected variants, exact citations, altered requirements, signs, endpoints,
child order and scope. All eight new pairs and three neighbors pass strict
Litex execution, independent byte-identical regeneration and fresh Lean 4.31.0
checks against the updated Core. Their 19 public declarations and four new
Core theorems use only `propext`, `Classical.choice` and `Quot.sound`. Each direct
additive example contains two universal statements and generates 3,449 bytes.
No Runtime, AST or result-producer changes were needed.

Componentwise addition was the next confirmed compiler gap at this checkpoint;
the following increment closes its four recorded variants. General
order-strategy coverage and nonliteral numeric weakening remain incomplete.

### Adding two order bounds, 2026-10-24

Four selected strategies now replay both original child proofs:

| Selected strategy | Core theorem |
| --- | --- |
| `AddComponentwiseLessEqual` | `Litex.addLeAdd` |
| `AddCrossedLessEqual` | `Litex.addLeAddSwap` |
| `AddComponentwiseStrictLeft` | `Litex.addLtAddOfLtOfLe` |
| `AddComponentwiseStrictRight` | `Litex.addLtAddOfLeOfLt` |

For example, `a <= b` and `c <= d` yield `a + c <= b + d`.
One strict premise yields a strict sum bound. The consumer validates both
sum constructors, the exact ordered child subjects, addend pairing and each
comparison's strength. It compiles children at their original source stages,
then applies the selected law to the existing WD-bearing sum objects.
Runtime, AST and result producers are unchanged; Core adds four proved laws.

The three pairs cover [weak and crossed bounds](../lean/examples/componentwise_sum_bounds/),
[strict/weak combinations](../lean/examples/mixed_strict_sum_bounds/) and
[a two-step three-term bound followed by theorem reuse](../lean/examples/three_term_sum_bound/).
Their generated files are 4,533, 4,551 and 43,884 bytes respectively.
All three and three related existing pairs pass strict Litex execution,
independent byte-identical generation and fresh Lean 4.31.0 checks. The twelve
exported declarations and four new Core laws use only `propext`,
`Classical.choice` and `Quot.sound`.

The compiler suite passes **956 tests**, including six new tests for the four
variants, composition, missing/reordered evidence, changed operand pairing or
comparison strength, and future/sibling citations. This adds proof routes
within existing statement and object families; it does not change the preceding
entrypoint counts. Mixed strict crossed-pair strategies are not claimed.

The next confirmed gap was subtracting a shared value; the following increment
closes its four selected strategy routes.

### Shared subtraction and strict order chains, 2026-10-24

Four subtraction strategies now compile:

| Selected strategy | Core theorem |
| --- | --- |
| `SubSharedSubtrahendLessEqual` | `Litex.subStructuralLeRight` |
| `SubSharedMinuendLessEqual` | `Litex.subStructuralLeLeft` |
| `SubSharedSubtrahendLess` | `Litex.subStructuralLtRight` |
| `SubSharedMinuendLess` | `Litex.subStructuralLtLeft` |

Each retains the original difference objects, their formation evidence and the
single recorded order proof. The consumer checks the common operand and the
reversed premise when the minuend is shared. Core uses real membership of the
difference, so the common operand can keep its original complex carrier.
Missing domain evidence, altered common operands or mismatched child subjects
are rejected.

The three-step difference example also exposed `LessTransitivity`. Its consumer
resolves the exact two cited FactIds, validates the intermediate endpoint and
both strictness flags, and applies existing `ltTrans`, `ltLeTrans` or `leLtTrans`.
Two weak premises cannot supply this strict conclusion. No extra search is run.

Five pairs cover [a shared subtrahend, including a compound expression](../lean/examples/subtract_shared_value/),
[a shared minuend](../lean/examples/subtract_from_shared_value/),
[real differences with a complex common operand](../lean/examples/real_difference_domains/),
[the three-step theorem and its call](../lean/examples/ordered_difference_bound/) and
[three strict-transitivity combinations](../lean/examples/strict_order_chains/).
All five and three related existing pairs pass strict Litex, byte-identical
regeneration and fresh Lean 4.31.0 checks. New generated files are 2,650–13,889
bytes. The seventeen checked public declarations and four new Core laws use
only `propext`, `Classical.choice` and `Quot.sound`.

The compiler suite passes **966 tests**, including ten new tests covering the
selected routes, domain evidence, citation scope, common operands, comparison
strengths and theorem composition. Runtime, AST and result producers are
unchanged. Statement/object entrypoint counts are unchanged.

Binary intersection was the next confirmed object gap; the following increment
adds its constructor, membership and subset routes.

### Binary intersection, 2026-10-24

`IntersectObj` retains the two original objects and denotes bounded separation
of the first by membership in the second. Its representation uses existing
`SetSemantics.sepValue`, `sep_members` and `sep_isSet`; the model interface has
no new fields or assumptions. Constructor compilation consumes the two ordered
child WD results. The compiler's existing traversal, parameter substitution and
denotation-template cases now recognize this constructor.

The checked proof paths are:

- `IntersectMembership`, both builtin and strategy variants, replaying the two
  original membership proofs in order through `inIntersect_iff`.
- `IntersectBoth` inference, validating and publishing both captured membership
  stores under distinct original FactIds for subsequent citations.
- `IntersectSubsetLeft` and `IntersectSubsetRight`, plus
  `IntersectSubsetFromLeftUpperBound` and `IntersectSubsetFromRightUpperBound`.
- `SubsetOfIntersectFromBothBounds`, preserving both ordered subset proofs.

Four pairs cover [membership and projections](../lean/examples/intersection_membership/),
[five subset bounds](../lean/examples/intersection_subset_bounds/),
[nested intersections and theorem reuse](../lean/examples/intersection_reassociation/),
and [a named set, membership transport and sethood](../lean/examples/named_intersection/).
All four and three related existing pairs pass strict Litex, independent
byte-identical regeneration and fresh Lean 4.31.0 checks. New files are
1,948–10,931 bytes. The 23 checked public declarations and six new Core laws
use only `propext`, `Classical.choice` and `Quot.sound`.

The compiler suite passes **976 tests**, including ten new tests for the
selected routes, missing/reordered WD and proof children, changed subset
subjects, future citations, projection order and reused FactIds. This increment
does not edit Runtime, AST or result producers. Against the original inventory,
coverage is **37/52 statement forms and 36/94 object constructors**.

The nested example above proves a membership statement. The next increment
adds the corresponding set-equality routes.

### Union and intersection equalities, 2026-10-24

Twelve original equality builtin variants now have consumers: union/intersection
commutativity, idempotence, left/right empty-set laws and associativity;
`IntersectUnionDistributive`; and `IntersectFromSubset`. The consumer validates
the selected constructor, exact operands and orientation. It projects child
objects from their existing WD producer. Conditional simplification consumes
the one recorded subset proof at its original scope.

Thirteen Core lemmas follow from existing separation/union membership laws
and set extensionality, without new model fields or assumptions. Runtime,
AST and result producers are unchanged by this increment.

Five pairs cover [intersection identities](../lean/examples/set_intersection_identities/),
[union identities](../lean/examples/set_union_identities/),
[conditional intersection simplification](../lean/examples/intersection_from_subset/),
[intersection distributed over union](../lean/examples/intersection_distributes_over_union/)
and [reversed equalities](../lean/examples/set_identity_symmetry/).
All five and three neighboring pairs pass strict source verification,
independent byte-identical regeneration and fresh Lean 4.31.0 checks.
New generated files are 2,305–12,161 bytes. Sixteen public declarations and
the thirteen Core lemmas use only `propext`, `Classical.choice` and `Quot.sound`.

The compiler suite passes **982 tests**, including six new tests covering all
selected rules in both directions, both conditional operand positions, changed
endpoints, a wrong selected rule, absent/extra/changed subset proofs and future
citations. Statement/object counts remain **37/52 and 36/94**: this increment
adds proof routes for existing constructors.

The following increment adds the opposite distribution law and set difference.

### Set difference and permuted distribution, 2026-10-24

`SetMinusObj` retains both original objects and denotes separation of the base
by nonmembership in the excluded set. Constructor compilation consumes both
ordered child WD results. Membership consumes the recorded positive and negative
children, in either the builtin or strategy result. The compiler emits the
original `SetMinusSplit` stores: base membership, exclusion and, when the
removed set is a singleton, disequality with its element. Their original FactIds
remain available to subsequent proof steps.

The checked proof routes also include exclusion from membership in the removed
set or nonmembership in the base, `SetMinusSubsetLeft`, self/empty differences,
both difference De Morgan laws and `IntersectSetMinusSelfEmpty`.
`UnionOverIntersectDistributive` now validates the two distributed factors and
composes the distribution, commutativity and congruence lemmas. Rust tests cover
all 32 combinations of operand order and equality direction.

Seven pairs cover [difference membership and projections](../lean/examples/set_difference_membership/),
[exclusion and subset](../lean/examples/set_difference_exclusion/),
[difference identities](../lean/examples/set_difference_identities/),
[reversed identities](../lean/examples/set_difference_symmetry/),
[named and nested difference theorems](../lean/examples/set_difference_theorem/),
[a set-valued function](../lean/examples/set_difference_function/), and
[permuted union distribution](../lean/examples/union_distributes_over_intersection/).
All seven and three neighboring pairs pass strict Litex, independent
byte-identical regeneration and fresh Lean 4.31.0 checks. New outputs are
4,234–34,229 bytes. Thirty public declarations and thirteen new Core laws use
only `propext`, `Classical.choice` and `Quot.sound`; the model gains no assumptions.

The compiler suite passes **994 tests**, including twelve new tests for WD,
ordered membership/strategy evidence, negative premises, inference identities,
singleton capture, equality directions and distribution permutations. Runtime,
AST and result producers are unchanged. Coverage is **37/52 statement forms
and 37/94 object constructors** against the original inventory.

One existing verifier boundary was exposed by this audit: it accepts
`union(A, intersect(B, A)) = intersect(union(A, B), union(A, B))`.
With `A = {}` and `B = {1}`, the left side is empty and the right side is `{1}`.
The compiler rejects this mismatched-factor result with no Lean output; the
upstream verifier matcher remains unchanged. The executable rejection is in
[the distribution tests](../tests/unit/compile_to_lean/set_difference_tests.rs).

The following increment closes the `SetMinusChainToUnion` gap identified here.

### Set chains and containment, 2026-10-24

`SetMinusChainToUnion` now compiles consecutive exclusions, including swapped
union operands and reversed equality. Eight atomic builtin consumers add
intersection/union nonmembership, subset transitivity, difference and power-set
monotonicity, and union containment by common or componentwise bounds. Four
strategy consumers carry upper bounds through unions, intersections and
differences using their original requirements and ordered proof children.

The componentwise union result omits syntactically reflexive pairs. The compiler
checks the exact direct/crossed pairing and emits `subsetRefl` only for those
pairs; all other pairs require their recorded proofs. Citation stages count
actual children, including the zero-, one- and two-child cases. No Runtime,
AST or result producer changes were needed.

Seven new pairs cover [consecutive differences](../lean/examples/consecutive_set_difference/),
[nonmembership](../lean/examples/set_operator_nonmembership/),
[monotonicity](../lean/examples/set_containment_monotonicity/),
[union bounds](../lean/examples/union_containment_bounds/),
[nested containment](../lean/examples/nested_set_containment/),
[a union-difference theorem](../lean/examples/union_difference_bound/) and
[an exclusion theorem](../lean/examples/outside_union_intersection/).
The two named theorems include subsequent calls.

All seven and three neighboring pairs pass strict source verification,
byte-identical regeneration and fresh Lean 4.31.0 checks. The new files are
3,568–12,482 bytes. The compiler suite passes **1,004 tests**, including ten new
tests for ordered/missing/changed premises, reflexive omissions and future
citations. All 39 public declarations and twelve new Core laws audited use only
`propext`, `Classical.choice` and `Quot.sound`. The semantic model gains no
assumptions. Statement/object counts remain **37/52 and 37/94**; this batch
extends proof routes within existing forms.

### Point and set preimage objects, 2026-10-24

`Preimage` and `PreimageSet` now compile their recorded operand WD, complete
function signature and checked bounded construction. Membership strategies
replay the ordered carrier, guard and output children. The named inference
results export their original base membership, guards and output FactIds;
the input-carrier subset rule uses the same complete-domain certificate.
Unary inputs remain unary, and multiple inputs retain the Cartesian tuple.

Core defines the set from the function graph and target. The chosen signature
certifies formation without changing denotation. The compiler validates the
captured builder's bound, parameter substitution, guards and output predicate;
it does not search for a replacement signature or proof. Inferred call objects
use the original membership evidence, with proof elimination confined to their
WD proofs. Runtime, AST and result producers are unchanged.

Four pairs cover [a guarded reciprocal](../lean/examples/guarded_reciprocal_preimages/),
[a binary quotient](../lean/examples/binary_quotient_preimages/),
[abstract functions](../lean/examples/abstract_function_preimages/) and
[positive inputs](../lean/examples/positive_domain_preimages/).
All four and three neighboring function/Cartesian pairs pass strict source,
byte-identical regeneration and Lean 4.31.0. The new files are 18,133–81,143
bytes. Unchanged bytes reused checks from this batch under the same Core and
toolchain. All 52 exported declarations, four new Core theorems and two
representation instances use only `propext`, `Classical.choice` and `Quot.sound`.

The compiler regression passed **1,011 tests**. Seven focused tests cover the
new sources and reject missing/reordered operands or children, changed bounds,
guards or targets, invalid tuple equality, wrong seed IDs and reused inference
IDs. The final local object-construction fix is checked again by this focused
module and the generated binary example. Counts against the initial inventory
are **37/52 statement forms and 39/94 object constructors**. Other complete-domain
evidence variants and the separate `Composition` constructor remain outside
this increment; native Adapter coverage has not been extended here.

## What can be a Lean wrapper

The external object contract remains `Obj α = { val : α, wd : WD val }`.
Membership remains a proposition. New numeric operations retain Litex-owned
constructors, with native observations and proved denotation laws supplying the
Mathlib connection. This plan does not retype a source variable after learning
that it belongs to a number set.

The table below describes target forms, not new accepted source examples.

| Litex form or result | Lean form | Condition to preserve |
| --- | --- | --- |
| `forall`, conjunction, disjunction, negation | `∀`, `And`, `Or`, `Not` with proof constructors/eliminators | Original parameter WD, premises, branch ownership and returned facts |
| `witness`, `obtain`, `have …` from known existence | `Exists.intro`, existential elimination or a selected witness | The recorded existential and its exact witness/property evidence |
| `exist!` | Existence plus uniqueness using `Litex.Same` | Native `ExistsUnique` uses Lean equality; it needs a faithful/quotient representation before substitution |
| `by cases`, finite enumeration, `by for` | `Or.elim`, finite eliminators and emitted proof applications | Exhaustive original cases and their local hypotheses; no fresh Lean proof search |
| Natural-number strong induction | A native natural representative and strong induction | Original starting domain, measure and inductive premises |
| `by extension`, `by fn_extension` | Proved set/function extensionality bridges | Source equality is `Litex.Same`; compare semantic members/outputs before concluding it |
| `prop`, `abstract_prop` | Definitions and predicate parameters | Abstract predicates must respect semantic equality, for example by operating on `M.Value` denotations |
| Verified `register` laws | Ordinary proved lemmas plus compiler references | Replay the returned verified `forall`; Lean does not need Litex's search registration mechanism |
| `struct`, field access, `template` | Structures/projections and parameterized definitions inside the object representation | Field domains, dependent WD and original parameter identities |
| Case-defined functions, functions from `exist!` | Conditional constructions or proved choice | Checked case coverage/uniqueness, domains, return facts and proof-independent denotation |
| Recursive functions and `algo` | Recursors or well-founded definitions behind the Litex function wrapper | The source's checked measure/termination evidence; start with the existing natural-number slice |
| `eval` | A checked evaluation equality | Replay its calculation certificate; command output alone is not a proof |

Logical wrappers are reusable across mathematical domains. They still cannot
compile a proof whose selected object, mathematical rule or inferred fact has
no adapter.

## From builtin rules to Lean theorems

Keep the two entrypoints distinct:

```text
automatic searched_proof variant -> matching compiler method -> proved Litex bridge
explicit BuiltinTheoremId        -> matching compiler method -> proved Litex bridge
```

They may call the same proved bridge when their premises and conclusions agree.
Each consumer still checks its own recorded arguments, WD, domain proofs,
selected conclusions and citations. The result enum remains the dispatcher;
no parallel theorem registry or new proof-search engine is needed.

Examples of planned mappings:

| Existing Litex rule/ID | Proved target |
| --- | --- |
| `SqrtProduct` | A Litex square-root product theorem proved through native real observations and `Real.sqrt_mul` |
| `SqrtOfSquareEqualsAbs` | A representation bridge followed by `Real.sqrt_sq_eq_abs` |
| `AbsProduct`, `MinCommutative`, `MaxCommutative` | Absolute-value and order laws, with the source operand domains retained |
| `UnionCommutative`, `IntersectCommutative` | Membership equivalences followed by semantic set extensionality |
| `SetBuilderMember`, `CartesianMemberFromCoordinates` | Existing bounded-builder and coordinate membership interfaces, with their recorded premises |
| `PrimeDividesProduct`, `PrimeDividesPower` | Native integer/natural primality and divisibility theorems after the exact carrier bridge |
| Finite sum comparison/substitution IDs | Finite enumeration/sum lemmas, respecting duplicate removal and source indexing |
| Limit, continuity and derivative IDs | The exact epsilon/domain contract connected to native analysis predicates, then the corresponding Mathlib law |

For example, the proposed route for `SqrtProduct` is:

```text
source operands a,b + recorded real/nonnegative evidence
  -> native real representatives and their denotation equations
  -> Real.sqrt_mul
  -> the Litex product/square-root denotation laws
  -> Litex.Same for the original source objects
```

It is not valid to emit a native theorem name before proving these conversions.
Negative square-root inputs, totalized division/logarithm, integer quotient and
remainder conventions, inverse trigonometric ranges, and punctured/one-sided
limits require explicit domain agreement.

A first elementary batch selected 21 equality branches:

- Square roots: `SqrtZero`, `SqrtOne`, `SqrtOfSquare`, `SqrtProduct`,
  `SqrtQuotient`, `SqrtOfSquareEqualsAbs`.
- Absolute values: `AbsOfNegation`, `AbsProduct`, `AbsSquare`,
  `AbsAbsAbsorption`, `AbsNonposEqualsNegation`.
- Powers: `NegativeIntegerPowerReciprocal`, `PowerOfProduct`,
  `ReciprocalAsNegOnePower`, `QuotientAsMulNegOnePower`, `OneToAnyPower`,
  `ZeroToPosNatPower`.
- Min/max: `MinIdempotent`, `MaxIdempotent`, `MinCommutative`, `MaxCommutative`.

The four min/max branches now have checked consumers and proved semantic
lemmas; the other 17 remain implementation work. Min/max accepts two real
operands with their recorded WD. Real/integer structural membership, nested
objects and aliases are checked. The follow-up also checks closed literal
arithmetic with min/max, including fractions, negatives, ties and nesting, plus
operand bounds and coordinatewise weak monotonicity. Its four non-equality
consumers retain the original comparison premises or `SameArgument` evidence.
See [evaluation](../lean/examples/min_max_evaluation/) and
[bounds](../lean/examples/min_max_bounds/).
The next increment supplies the four conditional selection consumers,
`MinLeftWhenLessEqual`, `MinRightWhenLessEqual`, `MaxLeftWhenLessEqual` and
`MaxRightWhenLessEqual`, with exact premise validation. Formula-body denotation,
parameter substitution and recorded nested-call expansion now handle min/max.
See [ordered selection](../lean/examples/ordered_min_max_selection/) and
[lower/upper functions](../lean/examples/ordered_min_max_functions/). The latter
combines `have fn`, a concrete `prop`, conditional `thm`, `let` and `by thm`,
including a clamp composed from two functions. Other extremum rules remain
separate work.

## Phases

The counts below allocate work remaining after the accepted checkpoint, not
estimates of development time. Predicate/proof/inference routes belong to each
phase as well; their work is not exhausted by the object count. An existing
entrypoint can also need broader domains or additional selected-proof branches.

| Phase | Deliverable | Remaining statement / object entries | Remaining explicit BT IDs |
| --- | --- | ---: | ---: |
| P0 | Current small failures repaired; retain the accepted baseline | 0 / 0 | 0 |
| P1 | Common proof statements and logical forms; broaden existing membership consumers where needed | 0 / 0 | 0 (four membership IDs delivered within their documented domains) |
| P2 | Elementary scalar operations and number theory | 0 / 0 | 4 |
| P3 | Set operations, finite collections and finite proof iteration | 0 / 20 | 12 |
| P4 | Function/structure/template interfaces and reusable proof declarations | 9 / 7 | 1 |
| P5 | Elementary transcendental and complex operations | 0 / 25 | 0 |
| P6 | Real analysis, delivered in five subphases | 0 / 8 | 340 |
| P7 | Explicit assumptions and foundation-model boundaries | 8 / 0 | 2 |

The remaining columns sum to 18 statement forms, 61 object constructors and
359 explicit BT IDs. The original P1 allocation was eleven forms and four BT
IDs. All eleven statement entrypoints now have focused Lean examples, including
object/tuple/Cartesian release, nonempty witnesses and `have` from existence.
The four membership IDs also have checked examples. These entrypoint counts do
not close the logical-form and evidence-variant gaps listed below. The three registration declarations also pass Lean;
reflexive/symmetric rewrite consumers have separate checked selected-stage
fixtures. Registered transitive-chain inference remains unsupported.
Set/function extensionality, strong induction and the two finite iteration
entrypoints have also passed the proof-command checkpoint; broader domains
within these entrypoints remain work for their respective phases.
`forall … iff` has checked shared-premise and local examples. Negated universals
now replay verified counterexamples, including local proof steps. Their separate
assumption/contra WD consumers and broader nested matching remain separate
work. Negative-existence contradiction/citation, unique-existence
witness/citation/obtain and automatic universal applications in all three
existential families now have checked pairs. Unique-existence function selection
also has four checked pairs. Remaining builtin and declaration routes are listed above.
Completing these inventories still requires the associated
WD, automatic rules, citations and inferred facts to be replayed.

P0 repairs the confirmed standalone `have a R+` semantic-parameter omission and
`$is_set(sqrt(4) + 1)` closed-membership failure. It also completes square-root
child reuse and reduces rendering that is discarded after finding a reference.
No whole-Geo gate is required.

P1 adds `have` from known existence, nonempty witnesses, the three verified
registration forms, object/cart/tuple definition release, set/function
extensionality and natural strong induction. Complete the logical interfaces
for `forall … iff`, negated universals, unique and negative existence within
the supported object domain. Connect explicit `fn_set_member`,
`set_builder_member`, `defined_set_member`, and `cart_member_from_coordinates`
through both checked invocation surfaces. Preserve the existing tuple adapter.
A definition-only wrapper for an abstract predicate can be introduced here if
needed; the complete declaration/instantiation interface belongs to P4.

Finish P1 in three batches: (1) existential introduction/elimination and the
remaining logical forms; (2) verified registration and object/cart/tuple
definition release; (3) set/function extensionality and strong induction.
Reuse the existing result dispatch and source-scoped citations in each batch.
Registration produces a proved law in Lean; subsequent reflexive, symmetric or
transitive uses must cite that law rather than export a runtime search flag.

P2 has added min/max and the sign slice: integer codomain, exact closed values,
positive/negative conditional equalities and formula/nested-call expansion.
The sign-of-product and sign-of-negation rules remain unimplemented.
Floor/ceiling now cover exact values, integer identities, the four defining
bounds, weak monotonicity and formula/nested-call expansion. Quotient/remainder
now cover signed evaluation, integer codomains, quotient identities, Euclidean
decomposition, remainder bounds, congruence and formula functions.
Gcd/lcm now cover signed values, N+/N codomains, eight equality rules, the
original nonzero-pair guard, gcd-modulus WD and formula-function use.
Factorial and the imaginary-unit literal now have checked constructor routes.
Factorial adds recurrences, nonzero and monotonicity; the imaginary unit supports
exact complex arithmetic and the selected polynomial-calculation tag.
All 15 numeric carriers now have checked representations, declarations and
function-domain use. P2 still needs unimplemented arithmetic/number-theory
proof routes and its four explicit BT adapters; its zero remaining
object-entry count does not complete those rules.
Start automatic equality work with the 21-rule batch above, then cover the
associated WD, closure, order, primality/divisibility and inference branches.
The four named BTs are reduced rational representation, gcd with a prime,
prime divisibility of a product, and prime divisibility of a power.

P3 adds the eight remaining set operators, four remaining set-former families,
six iterated operators and three finite-set statistics. Extend the current
independent list/range assignment products to dependent domains after reviewing
the source semantics; retain the checked integer-range expansion and add missing subset/nonmembership/finite predicates and their
inference rules. Sequence carriers may initially reuse the existing
unary function interface; general higher-order use is completed in P4.
The two indexed-cartesian choice theorems are reserved for P7.

P4 extends the checked unique-existence and case-defined function slices, then adds abstract predicates,
structures, templates, both algorithm definitions, reusable strategies,
preimage introductions, structure release and evaluation commands. Add the
four missing function-space constructors and structure/field/template objects.
Expand arity, dependent domains, higher-order use and recursion through checked
subsets. `f(g(x))` and the explicit `compose` object must both have evidence
coverage. The additional named BT is `struct_member`.

P5 adds `e`/`pi`, exp/log/ln, ten trigonometric, six hyperbolic and four complex
operators. Prove their WD and denotation interfaces before their automatic
identities and inequalities. This phase contributes many automatic rules even
though no remaining named BT ID is allocated to it.

P6 is five separate milestones, not one large integration task:

| Subphase | Scope | Explicit BT IDs |
| --- | --- | ---: |
| P6a | Real bounds/completeness, sequences, sequence limits/limsup/liminf | 90 |
| P6b | Function limits: finite points, sides, positive/negative infinity | 114 |
| P6c | Pointwise/global/uniform continuity and Lipschitz conditions | 77 |
| P6d | Derivatives and differentiability | 27 |
| P6e | Riemann integration and antiderivatives | 32 |

First establish the source/native predicate equivalence, including domains,
accumulation assumptions and interval endpoints. Then implement constant,
algebraic, comparison, existence/uniqueness and selected-value theorem families.
A common native lemma can serve several directional source IDs while each ID
retains its original conditions. The 340 IDs are a work inventory, not 340
independent axioms or 340 unrelated proofs.

P7 audits replacement, the three source trust/axiom forms, the three foundation
releases, plus the two indexed-cartesian choice BTs. Arbitrary source
`trust` cannot become an unconditional Lean proof. If assumption-preserving
export is wanted, its output must expose the assumptions. Choice, Zorn,
regularity and replacement need the appropriate represented domains and set
model; `Classical.choice` alone does not establish every set-theoretic contract.
`sketch` has been implemented separately as a checked, discarded local scope;
it introduces no assumption. Foundation/assumption policy remains a maintainer
choice before implementing that mode.

## Acceptance for each increment

### Earlier checkpoint: P0, P1 membership consumers and nonempty witnesses

- Standalone `have a R+` now includes the required set semantics. Exact closed
  square roots can feed arithmetic; a later occurrence of an already formed
  square-root child reuses its object reference.
- `set_builder_member` and `defined_set_member` consume their recorded premise
  proofs and stores. A selected theorem result also exports its recorded
  inferences for subsequent statements. A premise and return sharing a FactId
  become visible only after the original premise is proved.
- `witness $is_nonempty_set(S) from a` consumes both original WD results,
  its local proof body and the checked `a $in S`. It exports nonemptiness;
  local facts become unavailable after the witness body closes.
- Checks: 686 compiler tests; regeneration of all 94 current source pairs;
  ten affected/new pairs checked with Lean 4.31.0 (48 theorem declarations), with only `propext`,
  `Classical.choice` and `Quot.sound` in their axiom audit. These checks do not
  cover the ten P1 statement forms still pending at that checkpoint or the
  unfinished logical branches.

Examples: [square-root reuse](../lean/examples/square_root_subexpressions/statement.lit),
[exact square-root arithmetic](../lean/examples/exact_square_root_sum/statement.lit),
[builder membership](../lean/examples/positive_set_membership/statement.lit),
[named-set membership](../lean/examples/defined_positive_set_membership/statement.lit),
and [membership followed by a fact citation](../lean/examples/square_set_membership/statement.lit).
Each directory includes its generated Lean file.
The [nonempty-witness example](../lean/examples/nonempty_witness/statement.lit)
includes both a top-level builder witness and a singleton witness inside a theorem.

The next two P1 pairs also pass Lean and the axiom audit:
[Cartesian membership](../lean/examples/cart_membership_theorem/statement.lit)
includes a literal tuple and an arbitrary real pair; [function membership](../lean/examples/function_membership_theorem/statement.lit)
includes a formula, a named reciprocal, and a two-argument quotient. The
nonzero guards remain in the complete input domain when the return bound is
changed from real to complex. The generated files are about 23 KB and 36 KB.
Their bridges (`cart_of_coordinates`, `fnSet_of_returns`) are proved from the
existing function semantics. No new model assumption was added.

A separate existing gap remains: top-level `have point cart(R, R)` selects a
Cartesian nonemptiness strategy that the compiler does not yet replay. The
Cartesian BT example introduces arbitrary points as theorem parameters.

### Latest P1 increment: choices from existence and real-line witnesses

The [existential choice pair](../lean/examples/have_from_existence/statement.lit)
introduces a real equal to two, uses it in arithmetic, makes a local choice
inside a theorem, and extracts two objects with a nonzero divisor. Later uses
cite the returned properties and reconstruct division with the original WD.
`have` retains its source binder IDs; `obtain` keeps its separate fresh-name
requirement. Existentially bound occurrences retain lexical scope even when
the same ID also names an exported choice.

The [real-line witness pair](../lean/examples/real_line_witnesses/statement.lit)
covers all six comparisons, both operand orientations and one/two real binders.
It replays `RealLineComparisonWitness`, validates its original membership
children, and uses the proved `existsRealAbove` / `existsRealBelow` bridges.
Plain existential goals are also accepted by named theorem compilation.

Checks: 692 compiler tests passed; all 96 canonical source pairs regenerated
without drift. Both new pairs and the existing obtained-real-square pair passed
Lean 4.31.0, with 18 exported theorem declarations audited. Only `propext`,
`Classical.choice` and `Quot.sound` occurred. Generated sizes are approximately
15 KB and 22 KB for the new pairs. Runtime, AST and result types are unchanged;
Core adds two proved lemmas without new semantic assumptions. This completes
two of the original eleven P1 statement forms, not P1 as a whole.

### Universal conclusions supplying existential choices

The [choice-from-universal pair](../lean/examples/choice_from_universal/statement.lit)
uses a universal square-witness theorem to choose an object for an arbitrary
real. A second theorem gives a reciprocal witness under a nonzero premise;
its consumer makes the choice inside a theorem. Compilation checks the exact
cited conclusion, outer parameter substitution, inner witness renaming,
argument-match certificates and premise proofs. It invokes the existing
universal theorem and eliminates its existential result.

The generated 16 KB file passes Lean 4.31.0; its seven exported theorems use
only the standard `propext`, `Classical.choice` and `Quot.sound` axioms. Focused
rejection tests cover missing argument/premise evidence, changed patterns or
substitutions, a missing nonzero premise, and a citation to a later declaration.
The batch passed 695 compiler tests, and all 97 canonical pairs regenerated
without drift. No Runtime, result-type or Core changes were needed. This increment covers the
documented first-order argument certificates; more general nested binder
matching remains part of the unfinished logical work.

### Strict function composition

The five composition pairs cover a guarded two-input difference, shifted square,
double reciprocal with a nonzero outer condition, arbitrary real-function
parameters, and a positive-real inner domain. The compiler consumes original
composition WD, selected complete interfaces, argument checks and beta steps.
It does not replace the inner domain with a smaller compatible subset.
`CompositionObj` denotes graph composition independently of its WD proofs;
its Core laws follow from the existing function-graph interface.

See [the first pair](../lean/examples/squared_gap_composition/) and
[the compiler consumer](../src/compile_to_lean/compile_composition.rs).
These source/generated pairs pass strict source checking, identical regeneration
and Lean 4.31.0. Runtime, AST and result producers are unchanged.
The batch passes 1,017 compiler tests and eight real Lean checks (five new pairs
and three neighboring pairs). The 54 exported declarations, ten new Core laws
and one representation instance use only `propext`, `Classical.choice` and
`Quot.sound`. The new generated files occupy 41–97 KB. No native Adapter has
been added in this increment.
The statement count remains 37: this increment extends an object and the
existing declaration/call/proof paths. Object coverage increases from 39 to 40.
The next checkpoint below adds composition equality and range-subset
certificates. Cross-representation domain transport and dependent input domains
are not included in these checks.

### Composition graph laws

Three pairs replay the actual `CompositionAssociativity`, `CompositionLeftIdentity`,
`CompositionRightIdentity`, `CompositionDefinition` and `CompositionRangeSubset`
certificates: [formula functions](../lean/examples/composition_graph_laws/),
[nonzero guards](../lean/examples/guarded_composition_identities/) and
[arbitrary real functions](../lean/examples/abstract_composition_associativity/).
The definition cases include two inputs and a wider verified return carrier.
The Core laws follow from graph composition and extensionality; the compiler
validates the original operands, equality paths, lambda body and complete-domain
match. Source WD still certifies both sides before a fixed law is applied.

Checks: 1,024 compiler tests pass. The three new pairs and three neighboring
pairs pass strict source checking, identical regeneration and Lean 4.31.0.
Identical new outputs reused their checks under the unchanged Core/toolchain.
The 38 exported declarations and seven new Core laws use only `propext`,
`Classical.choice` and `Quot.sound`. The new files occupy 103–327 KB.

At this checkpoint right identity accepted only the alpha-equivalence branch.
The subsequent complete-domain increment below adds recorded mutual inclusion.
Dependent input domains and changes of packed-domain representation in composition
construction remain unsupported. No Runtime, AST, result
producer, model assumptions or native Adapter changes are part of this increment.
Counts remain 37/52 statement forms and 40/94 object constructors.

### Complete-domain comparisons and two-input function extensionality

`FunctionDomainComparisonProof::MutualInclusion` now compiles its actual forward
and reverse proofs. The consumer validates the quantified parameters, source
conditions and target memberships/guards, preserves each FactId, and derives
complete-domain equality with the existing set-extensionality law. Right
composition identity and `by fn_extension` share this consumer. The latter's
inclusion facts remain visible only inside its original proof scope.

`by fn_extension` also accepts two nondependent parameters and `R+` parameters.
The existing domain decomposition supplies the original memberships and guards;
tuple reconstruction transports the recorded pointwise equality to the original
input. Return bounds remain separate from graph equality.

Four new canonical pairs:

- [Positive shifts](../lean/examples/equal_positive_shifts/): different written
  positivity conditions, with the source's explicit order fact.
- [Reordered exclusions](../lean/examples/reordered_function_domains/): right
  identity and function extensionality with two reordered nonzero conditions.
- [Binary sums](../lean/examples/equal_binary_sums/): two inputs and positive-input
  doubling.
- [Guarded quotients](../lean/examples/equal_guarded_quotients/): two inputs,
  division WD, reordered guards, and different verified return bounds.

All 1,032 compiler tests pass, including eight new tests. The four new pairs and
three neighbors pass strict Litex, identical regeneration and Lean 4.31.0. Identical checked bytes reuse evidence under the unchanged Core
and toolchain; changed outputs receive fresh checks. The 60 exported declarations
use only `propext`, `Classical.choice` and `Quot.sound`. New generated files occupy
23–60 KB. No Core, Runtime, AST, result-producer or model-assumption changes.

Counts remain 37/52 statement forms and 40/94 object constructors: this increment
widens existing statement/result routes. More than two inputs to `by fn_extension`,
dependent domains and unimplemented complete-domain sources still reject.
At this checkpoint function-set membership still required alpha-equivalence;
the next increment below connects it to the same domain comparison consumer.
These consumers replay successful native certificates; automatic discovery of
domain equivalences is unchanged.

### Function-set membership with equivalent complete domains

Both `release thm fn_set_member(...)` and selected `by thm fn_set_member(...)`
now replay the recorded mutual-inclusion domain comparison before their original
return requirements. The graph's complete input domain is preserved while the
return bound may change using the checked pointwise proof. The source membership
consumer is shared with function extensionality and composition; duplicated
formula/citation branches and an unused generated target binding were removed.

Four additional pairs cover [reordered guards](../lean/examples/reordered_function_membership/),
[positive-real domains in both representations](../lean/examples/positive_function_membership/),
[cited arbitrary functions](../lean/examples/abstract_function_membership_domains/)
and [composed quotients](../lean/examples/composed_quotient_membership/).
The last consumes `CompleteFunctionDomainSourceProof::Composition`; no function
body is reconstructed from the environment. The original return proof and all
call WD remain required.

All 1,038 compiler tests pass, including six new tests. The four new pairs and
three neighbors pass strict source, identical regeneration and fresh Lean 4.31.0
checks. All 44 exported declarations use only `propext`, `Classical.choice` and
`Quot.sound`. New generated files occupy 35–118 KB. Controls reject swapped
inclusions, a forged alpha-equivalence result, future return citations and a
smaller domain substituted for the complete domain.

No Core, Runtime, AST, result-producer or model-assumption changes were required.
Counts remain 37/52 statement forms and 40/94 objects: existing theorem invocation
routes now cover more function sources and domain comparisons. Finite-source
membership retains its separate index-set/alpha-equivalence contract. General
dependent domains and unimplemented complete-domain source variants remain outside
this increment.


### Returned functions: calls, ranges and preimages (2026-10-24)

Function parameters with fixed function-valued returns now support successive
calls. Each layer replays its original arguments, membership proofs and guards;
two- and three-layer cases, two-input calls, nonzero guards and `R+` domains are
checked in [returned function values](../lean/examples/returned_function_values/).
`ApplicationReturn` also supplies the shared complete-domain consumer with its
original signature citation and scoped applicability evidence. This enables
[returned ranges](../lean/examples/returned_function_ranges/),
[returned preimages](../lean/examples/returned_function_preimages/) and
[a named membership theorem](../lean/examples/returned_function_membership/).

All **1,045 compiler tests** pass, including seven new tests. The four new pairs
and 58 related pairs have checked Lean 4.31.0 artifacts; unchanged hashes reused
this batch's earlier checks. The 421 exported theorems use only `propext`,
`Classical.choice` and `Quot.sound`. Independent native verification selected
different proofs on two existing examples; the final gate additionally checked
both outputs where that variation recurred. Deterministic replay tests use the
same typed result.

No Runtime, AST, result-producer, Core or model-law change was required. Counts
remain 37/52 statement forms and 40/94 objects. Dependent return signatures
and complete-domain recovery after several call layers remain pending.

### Constructed returned functions and function parameters (2026-10-24)

Three additional source/generated pairs pass strict Litex execution and Lean
4.31.0:

- [Anonymous function signatures](../lean/examples/literal_function_signatures/):
  membership in the declared function space, with renamed binders and unary or
  binary nonzero guards.
- [A returned shift](../lean/examples/selected_shift_function/): `have fn` returns
  a new anonymous function; `let`, explicit signature membership, range
  construction and equality substitution lead to `chosen_shift(2) = 3`.
- [The identity operator on functions](../lean/examples/function_identity_operator/):
  a function-valued parameter is returned unchanged, with a universal equality.

The new builtin consumer validates the entire declared signature, then uses
`Litex.formulaFnInFnSet` for the original checked constructor. Return-set alpha
equality reuses the existing identity consumer. Function-set values retain a
proof-valued header `let` and expose their constructor directly for elaboration
inside other signatures. Runtime, AST, result capture, Core and model laws are
unchanged. All **1,050 compiler tests** pass, including five new tests covering
the selected route, replay determinism and rejection of altered carriers,
guards, subjects or missing constructor WD.

The three new pairs and 44 affected existing pairs have checked Lean artifacts.
The final audit covers 313 exported theorems, using only `propext`,
`Classical.choice` and `Quot.sound`. Both observed outputs were checked for the
two existing sources whose independent native runs selected different proofs.

Statement/Obj constructor counts remain 37/52 and 40/94; these changes extend
the proof routes and combinations of existing constructors. Outer-parameter
capture was added in the following checkpoint.

### Captured numeric functions (2026-10-24)

The source `have fn shifted_by(t R) fn(x R) R = fn(x R) R {x + t}` now compiles,
including `shifted_by(t)(2) = 2 + t` for arbitrary real `t`. Four pairs cover
[real and positive shifts](../lean/examples/captured_shift_functions/),
[division with outer or inner nonzero conditions](../lean/examples/captured_division_functions/),
[two inner arguments](../lean/examples/captured_binary_functions/), and
[immediate application](../lean/examples/nested_function_application/).
They pass strict Litex and Lean 4.31.0; generated files occupy 13–66 KB.

The raw graph interpretation combines the original lexical parameter IDs.
Constructor WD and return membership still consume their original proofs.
Beta validation substitutes free outer IDs while preserving inner binders,
carriers and guards. Subsequent call groups must match `continued_body` exactly;
their equality follows by congruence. The single-step builtin rewrite retains
its requirement that no continuation be inserted. Runtime, AST, result capture,
Core and model laws are unchanged.

All **1,056 compiler tests** pass, including six new tests for replay,
signature/body/binder corruption, missing guards and changed continuation
arguments. The four new pairs and 68 related pairs have checked Lean artifacts;
the audit covers 509 exported theorems with only `propext`, `Classical.choice`
and `Quot.sound`. Unchanged generated bytes reuse their pinned checks.

This covers fixed numeric signatures. Dependent carrier sets and additional
complete-domain recovery routes remain pending. The native search did not prove
`positive_shift(t)(1) = 1 + t` in the attempted `R+` universal; the checked example
records its positive-real membership, while the real-valued shift separately
checks the universal evaluation equality. No native proof-search change was made.

### Top-level abstract predicates (2026-10-24)

`abstract_prop` now compiles as an arbitrary predicate parameter over `M.Value`
denotations. A `(Fin n → M.Value) → Prop` parameter preserves source arity,
including zero. It supplies no truth instance or definition to unfold. Semantic
equality transports both positive and negated properties by Lean congruence.

Five new source/generated pairs cover [property transport and named theorem calls](../lean/examples/abstract_property_transport/),
[binary relations and negation](../lean/examples/abstract_relation_transport/),
[function guards](../lean/examples/abstract_function_guard/),
[nullary propositions](../lean/examples/abstract_proposition_identity/) and
[interleaved object/predicate declarations](../lean/examples/abstract_property_context/).
All five pass strict Litex verification and Lean 4.31.0; generated files range
from 874 to 12,776 bytes.

The compiler resolves declarations from their original visible source prefix,
checks predicate identity and arity, and retains argument WD and exact fact
citations. Exported declarations receive their original predicate parameters
before existing object context arguments. Abstract predicates cannot acquire
concrete-definition inference results. Runtime, AST, result producers, Core and
model laws are unchanged; no compiler registry is added.

All **1,063 compiler tests** pass, including seven new tests for deterministic
replay and rejected missing/changed signatures, WD, declarations and inference
results. The final batch checks the five new and ten related source/generated
pairs; ten identical artifacts reuse their pinned Lean checks. The audit of
54 exported theorems finds only `propext`, `Classical.choice` and `Quot.sound`.

Statement coverage advances to **38/52 forms**; object coverage remains
**40/94 constructors**, within the documented boundaries of each route. Local
and qualified abstract declarations remain unsupported. This batch adds no
native Adapter interface and does not change source `trust` or axiom policy.

### Independent structure fields (2026-10-25)

Top-level structures with independent fields and no header parameters or
defining conditions now compile. Their carriers use the existing Cartesian
set representation; source instances retain generic host representations.
The declaration checks field WD and its local parameter inferences. Structure
membership consumes the original ordered tuple-field proofs or the complete
Cartesian membership, as selected by `StructObjMembership`.

Quantified structure parameters replay their automatically opened layer:
Cartesian membership, field/coordinate equalities, field memberships and
inferences, all under their original FactIds. Direct field access uses a
certified coordinate call. Rational normalization can consume a field as a
scalar only when its original field WD and a released numeric membership
supply the observation.

Five checked pairs cover [coordinate-pair membership](../lean/examples/coordinate_pair_membership/),
[field equalities and arithmetic](../lean/examples/coordinate_pair_fields/),
[mixed real/natural fields](../lean/examples/indexed_point_fields/),
[an arbitrary ambient carrier](../lean/examples/arbitrary_carrier_pairs/) and
[nested tuple membership](../lean/examples/nested_coordinate_membership/).
The nested example proves the inner membership explicitly before the outer
membership cites it. All five pass strict Litex and Lean 4.31.0, with generated
files between 3,745 and 26,317 bytes.

All **1,073 compiler tests** pass, including ten new tests for original result
replay, field WD/binder/order validation, missing or altered membership and
auto-open evidence, future release citations and nonnumeric field rejection.
The final batch covers five new and fourteen related pairs; fifteen identical
artifacts reuse their pinned checks. The audit of 116 exported theorems finds
only `propext`, `Classical.choice` and `Quot.sound`. Runtime, AST, result producers,
Core and model laws are unchanged.

Coverage advances to **39/52 statement forms and 42/94 object constructors**,
within this slice. Structure header parameters, dependent fields, `<=>`
conditions, nested field paths and local/qualified declarations remain to be
compiled. This checkpoint left ordinary structure bindings and explicit release
for the next increment, described below. No native Adapter interface is added
by this checkpoint.

### Structure bindings and explicit release (2026-10-25)

Independent-field structures now support `have p &CoordinatePair`,
`have origin &CoordinatePair = (0, 0)` and `release struct def p`, both at
file scope and inside supported proof blocks. The six new pairs are:

| Example | Checked route |
| --- | --- |
| [Chosen coordinate fields](../lean/examples/chosen_coordinate_fields/) | Witness nonemptiness, introduce two objects, cite real field memberships and add their coordinates |
| [The origin](../lean/examples/origin_coordinate_fields/) | Typed tuple alias, field/coordinate bridges and equality-class proofs of zero coordinates |
| [Explicit coordinate release](../lean/examples/released_coordinate_fields/) | Verify the receiver's membership, then publish the original ordered field stores |
| [Two-pair addition](../lean/examples/coordinate_pair_addition/) | Quantify two structure parameters and preserve their auto-open order |
| [Local coordinate objects](../lean/examples/local_coordinate_objects/) | Local choice, explicit release and a local typed alias inside a discarded sketch |
| [Coordinate field theorem](../lean/examples/coordinate_field_theorem/) | Replay structure release inside a named universal theorem |

Ordinary `have` consumes the captured nonempty proof. Typed aliases replay both
the temporary type preflight and the actual value/member checks. The preflight
is applied to those checked values, so its host universe is determined without
exporting its temporary facts. All actual membership, bridge and inference
stores retain their FactIds. Multiple layers use a borrowed ordered prefix;
parameter inferences cannot cite layers that have not yet been opened.

The batch adds seven compiler tests for result replay, missing/reordered layers,
altered subjects, separate preflight evidence and future fact/constructor
citations. All 1,080 compiler tests pass. Six new plus ten related source/generated
pairs pass strict Litex and Lean 4.31.0; unchanged generated bytes reuse their
pinned checks. The audit of 86 exported theorems finds only `propext`,
`Classical.choice` and `Quot.sound`. New files are 13–31 KB. Runtime, AST,
result producers, Core and model laws are unchanged. No project axioms or proof
holes are introduced.

Coverage reaches **40/52 statement forms and 42/94 object constructors** within
the documented slices. Field access and release currently require directly
declared structure parameters or typed aliases. Header parameters, dependent
fields, `<=>` conditions, nested field paths, function-call receivers and
local/qualified structure definitions remain separate work. The next semantic
increment is constrained carriers: membership must retain the defining
conditions and opening must release proofs of those conditions.

### Structures with defining conditions (2026-10-25)

Independent-field structures now retain supported `<=>` conditions. The carrier
is a bounded `Litex.setBuilder` over the Cartesian product. Membership consumes
the recorded field/carrier proofs and every condition proof. Automatic opening
and `release struct def` project the conditions under their original FactIds.
The original published universal laws retain their parameters, domains and IDs.

Condition WD follows source order: the denominator's nonzero fact can certify
a quotient in the next condition. Flat conjunction and chain projections are
available to subsequent conditions; private field assumptions stay inside the
declaration's formation check. Numeric field expressions reuse the existing
field constructors and released membership evidence.

| Example | Checked route |
| --- | --- |
| [Positive points](../lean/examples/positive_point_conditions/) | Literal membership, quantified condition release, and membership of an arbitrary Cartesian pair with a positive first coordinate |
| [Explicit positive-point release](../lean/examples/positive_point_release/) | Typed alias, explicit release and subsequent inequality/equality citations |
| [Positive ratios](../lean/examples/positive_ratio_conditions/) | Earlier nonzero condition supplies later division WD |
| [Ordered coordinates](../lean/examples/ordered_coordinate_conditions/) | Chain conditions retain their component facts |
| [First-quadrant points](../lean/examples/first_quadrant_conditions/) | Flat conjunction conditions retain both inequalities |
| [Chosen positive points](../lean/examples/chosen_positive_points/) | Nonempty witness, global/local choice, local typed alias and release |
| [Equal coordinates](../lean/examples/equal_coordinate_conditions/) | Equality conditions survive membership and opening |

All **1,087 compiler tests** pass, including seven new tests for deterministic
replay, missing/reordered conditions, membership obligations, release stores,
private/future citations, publication shape and invalid members. The seven new
pairs pass strict Litex, independent-run generation comparison and fresh Lean
4.31.0 checks with warnings treated as errors. Sixteen related pairs regenerate
unchanged and reuse their exact-byte Lean checks under the same Core/toolchain.
The audit of **151 exported theorems** finds only `propext`, `Classical.choice`
and `Quot.sound`. New generated files are 12–42 KB.

Runtime, AST, result producers, `Litex.lean` and model laws are unchanged.
This broadens existing entries, so the count stays **40/52 statement forms and
42/94 object constructors**. Conditions are limited to supported atomic, flat
conjunction and chain facts. Header parameters, dependent fields, quantified
conditions, nested field paths, function-call receivers and local/qualified
structure definitions remain unsupported. Header parameters and dependent
field carriers are the next structure increment.

### Parameterized structure families (2026-10-25)

Structure headers now accept set and object parameters. Later header parameters
may depend on earlier ones, as in `A set, a A`. Declaration compilation replays
their original introductions in a borrowed header scope. A specialized carrier
consumes the original ordered argument WD and instantiated type proofs;
membership, field release and published universal laws retain those arguments.
Field carriers remain independent of other fields but may use header parameters.

| Example | Checked route |
| --- | --- |
| [Parameterized pairs](../lean/examples/parameterized_pairs/) | Literal specialization to R and field membership over an arbitrary set |
| [Parameterized equal pairs](../lean/examples/parameterized_equal_pairs/) | A defining equality survives generic specialization and release |
| [Threshold points](../lean/examples/threshold_points/) | A real header parameter remains in the defining inequality |
| [Designated coordinates](../lean/examples/designated_coordinate_pairs/) | A later header parameter belongs to the earlier set; the first field equals that parameter |
| [Chosen parameterized pairs](../lean/examples/chosen_parameterized_pairs/) | Nonempty witness, ordinary have, global release and local typed alias/release |

All **1,093 compiler tests** pass. Six new tests cover deterministic replay,
missing/reordered introductions, missing/reordered argument WD and type proofs,
private/future header facts, published-law binders and premises, and an invalid
natural-number pair. Each new pair passed strict Litex, independent-run output
comparison and a fresh Lean 4.31.0 check. The final batch regenerates five new
and 23 related pairs identically, reusing the checked bytes under the same Core
and toolchain. The audit of **187 exported theorems** finds only `propext`,
`Classical.choice` and `Quot.sound`. New output sizes are 9–32 KB.

No Runtime, Env, AST, result-producer, Core or model-law change was needed.
Entry counts remain **40/52 statements and 42/94 objects**. Nonempty/finite-set
header kinds, fields depending on other fields, quantified defining conditions,
nested field paths, function-call receivers and local/qualified declarations
remain outside this slice. Dependent field carriers are next.

### Nonempty-set parameters and optional indexed unions (2026-10-25)

Structure headers, universal facts and named theorems now accept
`A nonempty_set`. The binder remains a generic certified object plus its
original `Litex.IsNonempty` FactId. Specialization and `by thm` consume the
recorded nonempty proof; sethood cannot substitute for it. Whole-forall reuse
preserves the binder kind and original citation under parameter renaming.

| Source/generated pair | Checked behavior |
| --- | --- |
| [Nonempty pairs](../lean/examples/nonempty_parameterized_pairs/) | Literal and generic specialization, coordinate membership, sethood and nonempty facts, whole-forall reuse |
| [Nonempty equal pairs](../lean/examples/nonempty_equal_pairs/) | A defining equality survives the nonempty header and field release |
| [Nonempty Cartesian product](../lean/examples/nonempty_cartesian_theorem/) | The selected product strategy consumes each factor's nonempty fact; a named theorem is reused with R and C |

All **1,099 compiler tests** pass, including six new tests for positive replay,
wrong/missing kind capture, missing nonempty evidence, sethood or wrong-subject
substitution, private/future facts, empty arguments and the finite-kind boundary.
All **31 source/generated pairs** in this batch passed strict Litex,
independent-run byte comparison and fresh Lean 4.31.0 checks under the updated
Core. The **199 exported theorem** audit finds only `propext`, `Classical.choice`
and `Quot.sound`. The three new generated files are 3,954–13,469 bytes; the
28 previous generated files are unchanged.

The maintainer selected a separate optional `IndexedUnionSemantics M` interface
for dependent carriers. Core now includes its indexed-union operation,
membership/sethood laws and a proved instance for the existing ZF model.
`SetSemantics` and existing generated theorem assumptions are unchanged.
Local handwritten checks cover empty indices, singleton fibers and dependent
coordinate pairs; these establish semantic feasibility, not compiler coverage.

Entry counts stay **40/52 statements and 42/94 objects**. No Runtime, Env, AST
or result-producer changes were needed. Dependent field replay is next; finite
binder kinds, standalone `have A nonempty_set`, quantified structure conditions,
nested field paths, function-call field receivers and local/qualified structure
definitions remain outside this slice.

### Ordered dependent structure fields (2026-10-25)

Field carriers can now refer to earlier fields. The compiler consumes the
declaration's original WD, parameter stores and inferences in order, emitting
a certified `Litex.DependentFields` family. `Litex.dependentCart` denotes its
valid flat tuples. This route uses the optional `IndexedUnionSemantics M`
interface selected in the preceding checkpoint; existing `SetSemantics`
implementations do not acquire a new field.

| Source/generated pair | Checked behavior |
| --- | --- |
| [Repeated coordinates](../lean/examples/repeated_coordinate_fields/) | `x R; y {x}`, literal membership, field release and equality |
| [Member pairs](../lean/examples/member_coordinate_pairs/) | `x A; y x`, generic set parameters and nested finite-set arguments |
| [Three coordinates](../lean/examples/repeated_coordinate_triples/) | Three ordered fields and equality propagation |
| [Positive repeated coordinates](../lean/examples/positive_repeated_coordinates/) | A dependent carrier restricted by a defining condition |
| [Equal coordinates from a Cartesian pair](../lean/examples/equal_coordinates_membership/) | Nonliteral Cartesian membership from the recorded complete-domain and coordinate proofs, followed by structure membership |
| [Reciprocal coordinates](../lean/examples/reciprocal_coordinate_fields/) | `x R+; y {1 / x}`, retained sign/nonzero inferences and division WD |
| [Chosen repeated coordinates](../lean/examples/chosen_repeated_coordinates/) | Nonempty witness, `have`, explicit release and a local typed alias |

Release reuses certified field carriers. Numbered source coordinates connect
to finite indices through one proved certificate per declaration. Later fields
can reference the objects produced by earlier parameter inferences; a singleton
membership inference retains the constructor subjects of its resulting equality.
Original FactIds and declaration-local boundaries are preserved. No Runtime,
Env, AST or result-producer changes were needed.

All **1,107 compiler tests** pass, including eight dependent-field tests for
successful replay, field/inference visibility, wrong or missing formation,
reordered membership evidence, altered release subjects, unequal singleton
coordinates and corrupted nonliteral Cartesian certificates.
All **38 related source/generated pairs** pass strict Litex verification,
independent-run byte comparison and fresh Lean 4.31.0 checks with the current
Core. The **256 exported theorem** audit finds only `propext`,
`Classical.choice` and `Quot.sound`. The seven new generated files contain
17,936–41,672 bytes; the previous 31 generated files are byte-for-byte unchanged.
Core checks also cover an empty first carrier and an empty
later fiber; neither produces a tuple.

At least two fields are required, with dependencies pointing backward.
Finite-set header kinds, quantified conditions, nested field paths,
function-call field receivers and local/qualified structure definitions remain
outside this slice. These seven examples establish this dependent-field route,
not unrestricted dependent structures or coverage of all field constructors.

### Remaining statement entrypoints: current audit (2026-10-25)

Re-expanding the current `Stmt` enums gives **52 leaf forms**. The compiler
dispatches 40 to consumers and directly rejects the following 12. This counts
entrypoints; supported consumers still have restrictions on objects, evidence
variants, parameter kinds and local declarations.

| Still rejected | Forms | Planned connection |
| --- | ---: | --- |
| `eval expression` | 1 | Replay source WD, cited equalities, computation evidence and the published result equality |
| `algo ... by cases`, `algo ... by induc` | 2 | Consume the retained `define_fn` result through the corresponding function-definition compiler, then connect checked evaluation paths |
| `strategy name:` | 1 | Compile its checked universal proof and replay subsequent `ByKnownStrategy` applications |
| `template<parameters>:` | 1 | Preserve template arguments and guards, then consume the actual specialized definition result |
| `have by replacement_axiom` | 1 | Prove the image-set bridge and consume the original relation/functionality and membership evidence |
| `release regularity_axiom`, `release axiom_of_choice`, `release zorn_lemma` | 3 | Supply proved model bridges for each foundation contract and replay its checked premises |
| `trust`, `trust have`, `axiom` | 3 | Keep rejected in the verified profile; any future assumptions profile must expose the assumptions in its Lean interface |

The next implementation batch should connect **`eval` and `algo`**. Start with
exact closed arithmetic such as `eval (1 + 2)^2`, then retained equality
citations such as `have a R = 10; eval a + 1`, then the existing piecewise and
decreasing-recursive algorithm examples. A later assertion of the computed
equality must cite the original published FactId. Each stage needs a generated
Lean pair and rejection checks for changed values, missing WD/citations and
out-of-scope results. Aggregate, matrix and other evaluation families require
their own recorded-certificate adapters; an `eval` entrypoint does not cover
them automatically.

After that, connect `strategy` declaration and application together. Its current
result retains goal WD, body results, conclusion proofs and a local environment,
but not the declaration or ordered parameter/premise introductions. Inspect and
retain that original producer evidence before adding the consumer; do not
reconstruct it from the final environment. Templates and the four foundation
statements follow as separate batches with their own semantic contracts.

Existing-entrypoint extensions remain separate: `have A nonempty_set`, finite-set
parameter kinds, local declarations, and structure receivers such as nested
field access. They do not add new rows to the 52-form count.

Audit anchors: [statement enums](../src/ast/stmt.rs),
[statement dispatch](../src/compile_to_lean/compile_stmt_result.rs),
[definition dispatch](../src/compile_to_lean/compile_definition_stmt_result.rs),
[object declarations](../src/compile_to_lean/compile_define_obj_stmt_result.rs),
[releases](../src/compile_to_lean/compile_release_and_expand_result.rs),
[eval results](../src/execute/execute_eval_stmt/result.rs) and
[strategy results](../src/execute/execute_def_strategy_stmt/exec_def_strategy_stmt.rs).

### Per-route checks

Each tracked route needs:

1. The actual typed result variant and its original source example.
2. Object/WD and native-denotation interfaces, if new.
3. A Lean theorem or logical proof constructor consuming the exact evidence.
4. Compiler dispatch, citation and store/inference wiring.
5. One generated example checked by Lean, plus the nearest missing-premise,
   wrong-citation or wrong-domain rejection when applicable.
6. A native consumer when the phase claims a new native mathematical interface.

Implement and check one route at a time. Run compiler regression and affected
canonical pairs once per coherent batch; reuse unchanged artifacts' pinned
checks. Do not run Geo, local textbooks or all repository tests for each branch.
Keep `lean/Litex.lean` as the semantic owner and `lean/examples` as the generated
pair collection. Checks and inventory tooling remain local under `scripts/`.

This plan does not change Runtime or result storage. If an existing result lacks
necessary evidence, identify that exact producer gap before widening the task.
The coverage ledger must distinguish planned, rendered, replayed, Lean-checked
and native-consumer-checked routes. No unsupported route is to become `sorry`
or an invented axiom merely to complete the inventory.


### Explicit assumptions and foundation releases (2026-10-25)

This increment adds these paths:

| Source | Generated interface | Example |
| --- | --- | --- |
| Top-level `trust` | Explicit `h_<FactId>` hypotheses, with original WD and inferred stores | [Positive bound](../lean/examples/assumed_positive_bound/statement.lit) |
| User `axiom` | An explicit universal hypothesis, usable by direct citation, `release thm` and `by thm` | [Predicate instances](../lean/examples/assumed_predicate_instances/statement.lit) |
| `release regularity_axiom(A)` | `Litex.regularity`, using the recorded nonempty proof and publication WD | [Singleton regularity](../lean/examples/regularity_singleton/statement.lit) |
| `have by replacement_axiom` | `Litex.replacement`, consuming the exact recorded uniqueness citation; introduction and elimination keep their FactIds | [Identity image](../lean/examples/identity_replacement/statement.lit) |
| `release axiom_of_choice` | `Litex.choiceForIdentity`, constructing a graph from the recorded nonempty-family proof | [Family choice](../lean/examples/nonempty_family_choice/statement.lit) |
| `release zorn_lemma` | `Litex.zornMaximal`, replaying nonemptiness, the order laws and chain upper bounds | [Maximal element](../lean/examples/poset_maximal_element/statement.lit) |

The two assumption examples intentionally run without `-strict`. Their generated
theorems state the assumptions as parameters; they do not introduce Lean axioms.
A universal hypothesis quantifies over `Litex.Obj M.Value`. Its citation bridge
accepts arbitrary certified host objects through their denotations, avoiding a
fixed host-universe restriction on hypotheses.

Regularity requires the optional `RegularitySemantics M`, with its ZF instance
proved from Mathlib's regularity theorem. Replacement reuses
`IndexedUnionSemantics M`: bounded separation, singleton images and indexed union
construct the image of a possibly partial functional relation. It requires
uniqueness, not totality. Choice uses `FunctionSemantics M` and
`IndexedUnionSemantics M`; Zorn uses `SetSemantics M` and Mathlib's theorem on
bounded chains. Both releases retain each obligation's verification followed by
its original WD/store result, and the final conclusion's WD. Local proof facts
remain inside the release block.

`objectAtLevel` represents a certified semantic value in a singleton host type.
It lets these bridges apply local universal premises whose host universe is
already fixed. Its denotation is definitionally the original value; it adds no
model law or axiom. Concrete predicate definitions may contain a universal body,
as used by the upper-bound and maximal-element predicates in the Zorn example.

The six pairs pass source verification, independent-run regeneration and real
Lean checking. The four foundation examples use strict source mode. Generated
files are approximately 1–17 KB; their 20 exported theorems use only `propext`,
`Classical.choice` and `Quot.sound`. The compiler regression has **1120 passing
tests**, including missing and reordered obligation evidence. Four existing
predicate, theorem and structure examples are checked alongside this batch.

At this checkpoint, local trust closures, `trust have` and template specialization
were pending. The continuation below adds bounded consumers for them. Quantified-iff
assumptions and local replacement declarations remain unsupported. A standalone
family-union construction is not yet a separately accepted entrypoint; its checked
use here is inside choice's function signature. The older statement-count audit
above predates these increments.


### Template aliases and scoped assumptions (2026-10-25)

| Source | Generated interface | Checked pair |
| --- | --- | --- |
| `trust have denominator R: denominator != 0` | Object, real membership and nonzero fact are explicit parameters; reciprocal WD cites those facts. | [Nonzero denominator](../lean/examples/assumed_nonzero_denominator/statement.lit) / [Lean](../lean/examples/assumed_nonzero_denominator/statement.lean) |
| `trust have A set, a A` | Dependent object parameters retain their original membership FactIds. | [Set member](../lean/examples/assumed_set_member/statement.lit) / [Lean](../lean/examples/assumed_set_member/statement.lean) |
| `trust x > 0` inside a theorem with premise `$admissible(x)` | An explicit hypothesis states that every admissible real is positive. The theorem conclusion is unchanged; `by thm` passes the hypothesis. | [Admissible reals](../lean/examples/admissible_reals_assumption/statement.lit) / [Lean](../lean/examples/admissible_reals_assumption/statement.lean) |
| `template<S set>: have carrier_copy set = S` | A parameterized semantic object plus the original published sethood and equality facts. | [Carrier copy](../lean/examples/template_carrier_copy/statement.lit) / [Lean](../lean/examples/template_carrier_copy/statement.lean) |
| `template<x R, y R: y != 0,>: have quotient R = x / y` | Each instance consumes the recorded argument WD, membership and nonzero proofs; unfolding replays the original residual equality. | [Guarded quotient](../lean/examples/template_guarded_quotient/statement.lit) / [Lean](../lean/examples/template_guarded_quotient/statement.lean) |

Template results now hold `Box<ExecStmtResult>` instead of a separate success-only
body enum. Parameter/domain stages and local environments retain their original
execution order. Domain assumptions reuse `AssumeDomFactResult`. Detailed JSON
includes `introduced_params`, `assumed_dom_facts`, the ordinary `body` projection
and the existing publication links. The parser, AST, Runtime storage and proof
search are unchanged.

Closure hypotheses quantify over `Litex.Obj M.Value`; a generic source object is
passed through its certified denotation. This keeps membership as a proposition
and allows a theorem to be instantiated at another host universe. No new Core
axiom or semantic class is needed.

The five new pairs pass source verification, independent-run byte comparison and
real Lean checking. The two template examples use strict source mode; the three
assumption examples use non-strict mode. Outputs are approximately 1.4–7.3 KB.
All 13 exported theorem audits contain only `propext`, `Classical.choice` and
`Quot.sound`. Core is unchanged from the preceding checked foundation increment.

The final batch also rechecks six existing assumption, theorem, structure and
foundation pairs: **11 pairs and 46 exported theorem audits pass**. Existing
generated files are unchanged. Rust checks pass **1132 compiler tests**, **82
template-related tests** and **13 statement-boundary tests**; these filters overlap
and are not a combined distinct-test count. The final CLI build also succeeds.

Current boundaries: template bodies are single typed object aliases. Function,
existential-choice and trust-have template bodies, local template declarations
and template-as-carrier inference are not covered by this increment. Local trust
supports the replayed claim/theorem/sketch block family; local `trust have`,
closures after local witness extraction, other proof-control families and locally
trusted universal statements remain rejected. These boundaries reject the whole
Lean artifact rather than omitting a source step.

### Current object inventory, 2026-10-25

The current AST has **128 object constructor leaves**, using the same counting
method as the original inventory: operation-family variants are separate entries;
`Identifier`, `StandardSet`, calls and template instances each count once.
There are **73 constructor entrypoints**, including the finite-set statistics,
aggregates, intervals/sequences, exponential/logarithmic objects, all ten
trigonometric constructors and complex observations checked below, and
**55 without a WD construction consumer**:

| Missing family | Source objects / AST variants | Count |
| --- | --- | ---: |
| General folds | `reduce`, `finite_set_reduce` | 2 |
| Hyperbolic functions | All 6 `HyperbolicOperator` variants | 6 |
| Set families | `SymmetricDifference`, `FamilyIntersect`, `IndexUnion`, `IndexIntersect`, `IndexCart` | 5 |
| Real analysis | Supremum/infimum, six limit selectors, ten derivative operators, Riemann integral | 19 |
| Matrices and finite-dimensional operations | `MatrixSet` and all 22 `MatrixOperator` variants | 23 |

This measures constructor dispatch, not complete proof-rule coverage. For example,
`range`, `closed_range`, `finite_seq`, real intervals/rays and `seq` have consumers. All four `ExpLogOperator` constructors now have consumers. `family_union` is supported. The optional `IndexedUnionSemantics` used by
dependent structures does not yet compile the source `index_union(I, X, A)` object.
Function/template objects also retain the signature, body and scope boundaries
described in their checkpoints.

### Finite-set cardinality and extrema, 2026-10-25

These statements now compile through their original WD and selected calculation
or extremum-selection result:

```litex
finite_set_size({1, 2}) = 2
finite_set_max({1 / 3, 1 / 2}) = 1 / 2
```

The objects carry finiteness evidence. Maximum and minimum also carry the
original nonempty and real-subset proofs. Core defines cardinality from semantic
membership and extrema from the real representatives of members; denotations
are independent of these proofs. The bridge laws are proved from the existing
semantic interfaces and Mathlib, without new model fields or project axioms.

| Checked use | Source and generated Lean |
| --- | --- |
| Empty/nonempty cardinality and nested arithmetic | [Finite collection cardinality](../lean/examples/finite_collection_cardinality/) |
| Maximum/minimum selection, including exact fractions | [Finite collection extrema](../lean/examples/finite_collection_extrema/) |
| Arbitrary finite-set cardinality in N and nonnegativity | [Cardinality bounds](../lean/examples/finite_set_size_bounds/) |
| Minimum/maximum bounds and extremum membership for arbitrary finite real sets | [Finite real-set bounds](../lean/examples/finite_real_set_bounds/) |
| `finite_set` theorem parameters and a selected theorem call | [Cardinality theorem](../lean/examples/finite_cardinality_theorem/) |

All five pairs pass strict source verification, independent-run regeneration and
Lean 4.31.0. The final batch also checks three existing min/max, finite-sequence
and template pairs. Four unchanged outputs reuse their earlier checks against
the identical Core/toolchain; the other four receive fresh Lean checks. All 28
exported theorem audits use only `propext`, `Classical.choice` and `Quot.sound`.
The compiler suite passes **1143 tests**, including 11 finite-statistics tests
covering altered selections, missing/reordered WD, empty extrema and nonreal
inputs. New outputs are 2.0–39.4 KB. No AST, Runtime or result-producer change
was needed.

Current boundaries: automatic finiteness replay accepts finite enumerations and
existing cited finite facts; other finiteness rules remain unsupported. These
statistics are not yet supported as formula-function bodies, and `finite_set`
structure headers remain rejected. Range and finite-set sums/products are
covered by the following checkpoints; general folds remain unsupported.

### Integer-range sums and products, 2026-10-25

The compiler now replays these finite calculations:

```litex
sum(1, 3, fn(x Z) Z {x}) = 6
sum(-2, 2, fn(x Z) Z {x * x}) = 10
product(1, 3, fn(x Z) Z {x}) = 6
```

`RangeAggregateObj` retains the original certified endpoints and function. Its
WD contains integer endpoint membership, endpoint order, the selected function
membership, output inclusion in C and domain coverage. Its denotation uses
Mathlib's finite sum/product over `Finset.Icc`; the function remains a Litex
object. Numeric observations depend on the fixed denotation, not on the WD proof.
All added Core laws are proved from the existing semantic interfaces.

The original aggregate WD results now retain `signature_selection`, including
the exact FactId for a named function's selected membership. Detailed JSON and
reading capture retain it too. This is a local result-capture change: AST shapes,
runtime storage, candidate order and verification behavior are unchanged.
Finite-set sum/product results also retain this field; their consumers are
covered by the following checkpoint.

For `AggregateCalculation`, the compiler consumes the recorded index range,
checked applications, function-equality citations, substituted bodies, term
values and accumulated values. It emits one checked call calculation per term
and a finite fold. It rejects missing or inconsistent evidence.

| Checked use | Source and generated Lean |
| --- | --- |
| Integer sums and negative indices | [Integer-range sums](../lean/examples/integer_range_sums/) |
| Integer products | [Integer-range products](../lean/examples/integer_range_products/) |
| Exact rational terms | [Rational sum](../lean/examples/rational_range_sum/) |
| Named function reused in a sum and a product | [Named aggregates](../lean/examples/named_range_aggregates/) |
| Arbitrary real-valued functions and symbolic endpoints | [Scalar closure](../lean/examples/range_scalar_closure/) |

All five pairs pass strict source verification, independent-run regeneration
and Lean 4.31.0. After the shared call-denotation update below, their generated
files are 6.3–30.7 KB.
The compiler suite passes **1149 tests**, including six aggregate tests with
original FactId/JSON checks, rejected domains and altered-evidence controls.
The batch also checks three neighboring range, finite-cardinality and returned
function examples. All 17 exported theorem audits use only `propext`,
`Classical.choice` and `Quot.sound`. The five aggregate outputs reuse their
just-completed checks against identical bytes, Core and toolchain; the three
neighboring pairs receive fresh Lean checks.

Current constructor boundary: an ordered closed integer range and an unguarded
unary function whose input is Z, Q, R or C. The generic output-closure consumer
accepts standard numeric output sets. Direct calculation currently accepts
closed scalar bodies built from numbers, addition, subtraction, multiplication,
division and negation. Folds, additional domain guards,
natural-only input domains, nested aggregates, algorithm iterands, matrix terms
and additional rewrite/evaluation stages remain rejected. This is constructor
and selected-rule coverage, not support for every theorem about sums/products.

### Finite-set sums and products, 2026-10-25

The same calculation replay now supports finite-set aggregates, including a
named set and a named function:

```litex
have finite_aggregate_set set = {2, 4, 7}
have fn aggregate_successor(x Z) Z = x + 1
finite_set_sum(finite_aggregate_set, aggregate_successor) = 16
finite_set_product(finite_aggregate_set, aggregate_successor) = 120
```

`FiniteAggregateObj` retains the certified set and function, selected signature
and numeric input carrier. Its WD consumes the original finiteness, input-subset,
output-subset and function-membership proofs. Denotation folds over semantic
members, independently of these proofs. The empty sum is zero and the empty
product is one. Core's calculation bridge proves that a recorded enumeration
has exactly those members before folding the checked function calls.

The compiler replays the existing set-equality path, enumeration order, call WD,
substituted bodies and accumulated values. Finite-set aliases also use a newly
supported `IsFiniteSet` equality-transport branch, consuming the original cited
equalities. No runtime or result-producer changes were needed in this increment.

| Checked use | Source and generated Lean |
| --- | --- |
| Empty and nonempty integer sums | [Finite collection sums](../lean/examples/finite_collection_sums/) |
| Empty and nonempty integer products | [Finite collection products](../lean/examples/finite_collection_products/) |
| Exact rational inputs and outputs | [Rational aggregates](../lean/examples/finite_rational_aggregates/) |
| Named set and function, with original equality citations | [Named finite aggregates](../lean/examples/named_finite_aggregates/) |
| Arbitrary finite real sets and arbitrary real-valued functions | [Finite aggregate closure](../lean/examples/finite_aggregate_closure/) |

All five pairs pass strict source verification, independent-run regeneration and
Lean 4.31.0. Their generated outputs are 6.3–43.5 KB.
The compiler suite passes **1154 tests**, including 11 aggregate tests covering
missing WD, changed enumerations and accumulated values, lost/duplicated equality
citations and unsupported guards. The final checks include four affected
integer-range examples, for nine pairs in total. All 21 exported theorem audits
use only `propext`, `Classical.choice` and `Quot.sound`. Two outputs reuse their
just-completed checks against identical bytes, Core and toolchain; the other
seven receive fresh Lean checks. Shared call replay now transports the actual
argument denotation explicitly, including rational arguments.

Current boundary: unguarded unary numeric functions and standard numeric output
closure. Concrete calculations consume list-set enumerations with exact rational
elements and closed scalar bodies; set aliases may use their recorded equality
paths. Range-shaped enumerations, additional numeric rewrite stages, guards,
nested aggregates, algorithm iterands and general folds remain unsupported.
Generic constructor/output closure does not require an enumerated literal set.

### Real intervals, rays and sequence spaces, 2026-10-25

The compiler now constructs bounded real intervals, real rays and `seq(S)`,
including arbitrary endpoints and carriers:

```litex
forall a, b, x R:
    a < x
    x <= b
    =>:
        x $in '(a, b]

forall A set, s seq(A), n N+:
    s(n) $in A
```

Interval and ray objects own their certified endpoints and consume the original
real-membership WD. Their denotations are bounded separation from R. Endpoint
order is not a formation requirement: reversed intervals remain legal sets.
Membership, open-endpoint/outside exclusion, inclusion in R and inferred endpoint
bounds replay the selected results and retain their original FactIds.

`seq(S)` owns its certified carrier. Its denotation is the function space from
N+ to S, with indices starting at 1. The compiler proves the recorded equality
with `fn(k N+) S` in either orientation. A sequence-member expansion emits the
original function-membership fact; subsequent calls cite it. Finite and infinite
sequences share that emission code while validating their distinct source rules.
No AST, Runtime or result-producer change was needed for this increment. Core
uses the existing set/function semantic interfaces without new model fields or
project axioms.

| Checked use | Source and generated Lean |
| --- | --- |
| Four bounded interval shapes, endpoints and reversed-interval sethood | [Interval endpoints](../lean/examples/real_interval_endpoints/) |
| Four real ray shapes, endpoints and exclusion | [Ray endpoints](../lean/examples/real_ray_endpoints/) |
| Original real-membership and bound facts for arbitrary elements | [Interval bounds](../lean/examples/real_interval_bounds/) |
| Membership and exclusion from symbolic bounds | [Symbolic membership](../lean/examples/real_interval_membership/) |
| Arbitrary carriers, aliases, nested sequence spaces and function-space equality | [Sequence spaces](../lean/examples/infinite_sequence_spaces/) |
| Calls into arbitrary carriers at positive-natural indices | [Sequence values](../lean/examples/infinite_sequence_values/) |

All six pairs pass strict source verification, independent-run regeneration and
Lean 4.31.0. Their outputs are 5.9–20.7 KB. The compiler suite passes **1162 tests**,
including eight interval/sequence tests. Controls reject missing/reordered WD,
reversed bound evidence, altered stored subjects/FactIds, a changed sequence
index domain or result carrier, and a mismatched expansion rule. Open endpoints,
nonreal interval endpoints and sequence calls at zero remain rejected.
The final batch checks ten pairs, including the existing finite-sequence spaces,
finite-sequence coordinates, integer-range bounds and set-builder unit interval.
Six unchanged outputs reuse the checks just completed against identical Core,
bytes and toolchain; the four neighboring pairs receive fresh Lean checks.
All 76 exported theorem audits use only `propext`, `Classical.choice` and
`Quot.sound`.

This covers construction and the listed proof routes. General interval algebra,
additional sequence membership rules, convergence and limit selectors remain
outside this increment.

### Constants, exponential and logarithmic objects, 2026-10-25

These source statements now compile with their original WD and proof results:

```litex
forall x R:
    ln(exp(x)) = x

log(8, 4) = 2 / 3

have fn exponential_value(x R) R+ = exp(x)
have fn natural_logarithm_value(x R+) R = ln(x)
forall x R:
    natural_logarithm_value(exponential_value(x)) = x
```

`e` and `pi` use native numeric payloads, denoting Mathlib's `Real.exp 1` and
`Real.pi`. `ExpObj`, `LnObj` and `LogObj` own their certified arguments. Exponential
WD requires R membership; logarithm WD requires R+ membership. The two-argument
logarithm retains both real memberships, both positivity proofs and the original
base-not-one proof. Its denotation is `Real.log argument / Real.log base` through
the existing numeric embedding. None of these denotations depends on the chosen
WD proof, and no new semantic model fields or project axioms were added.

The consumers replay intrinsic codomain proofs, exp/ln inverse identities,
`e = exp(1)`, `ln(e) = 1`, and logarithms of one or the base. Basic log rules retain
the original above-one, below-one or positive-nonunit evidence. Closed values
are checked against the original calculation result. An exact rational logarithm
p/q additionally checks `argument^q = base^p` in Lean, then applies proved log
laws; it does not use floating-point approximations. Arithmetic normalization
may treat these defined scalar values as opaque leaves. Formula functions keep
their Litex representations and replay the recorded parameter substitution and
function expansions.

| Checked use | Source and generated Lean |
| --- | --- |
| Symbolic exp/ln inverse identities | [Inverse identities](../lean/examples/exponential_logarithm_inverse/) |
| Positive e and pi; their exp/ln identities | [Mathematical constants](../lean/examples/positive_mathematical_constants/) |
| Arbitrary positive nonunit bases and positive arguments | [Real log output](../lean/examples/logarithm_real_output/) |
| Exact values, including `log(8,4)=2/3` and a base below one | [Exact values](../lean/examples/exponential_logarithm_values/) |
| Three original base-guard routes | [Unit identities](../lean/examples/logarithm_unit_identities/) |
| Formula functions, composition and scalar arithmetic | [Functions](../lean/examples/exponential_logarithm_functions/) |

All six pairs pass strict source verification, independent-run regeneration and
Lean 4.31.0. Generated outputs are 3.6–31.3 KB. Six focused Rust tests cover
missing/swapped WD, wrong carriers or nonunit evidence, a missing inverse premise,
changed calculation results and rejected source domains. The compiler regression
passes **1168 tests**. The final Lean batch checks nine pairs, including existing
square-root, nested-call and range-sum neighbors; three identical outputs reuse
checks from this increment and six receive fresh checks. All 42 exported theorem
audits use only `propext`, `Classical.choice` and `Quot.sound`.

This increment does not cover every exp/log proof rule. General exp/log algebra,
monotonicity and injectivity routes, real-exponent laws and further analytic rules
still require their own result consumers. `ln(0)`, a unit or negative logarithm
base, and `exp(i)` remain outside the source domains. AST, Runtime and result
producer contracts are unchanged.

### Sine, cosine and tangent, 2026-10-25

These statements compile through their original WD and selected proof results:

```litex
forall x R:
    sin(x)^2 + cos(x)^2 = 1

forall x R:
    cos(x) != 0
    =>:
        tan(x) = sin(x) / cos(x)

sin(13 * pi / 6) = 1 / 2
tan(pi / 6) = sqrt(3) / 3
```

`SinObj`, `CosObj` and `TanObj` own their arguments. Sine and cosine retain the
real-membership proof; tangent also retains the original cosine-nonzero proof.
Their fixed denotations wrap Mathlib's real trigonometric functions. The source
result selects each value or identity adapter; the compiler does not search for
a different proof. All new Core bridge theorems are proved, with no new semantic
model fields, project axioms, AST fields, Runtime changes or result changes.

The periodic-value consumer validates the captured pi coefficient and recorded
value. It currently accepts closed rational coefficients: it checks the integer
period and quadrant reduction in Lean and uses the standard exact-angle table
at 0, pi/6, pi/4, pi/3 and pi/2. The related nonzero consumer supplies tangent WD
at supported angles. Exact rational radicands can now expose their native
`Real.sqrt` denotation; they remain exact radicals. Symbolic square roots keep
their existing representation. Generated headers include the set interface when
native constants' intrinsic R+ evidence is used inside an expression.

| Checked use | Source and generated Lean |
| --- | --- |
| Zero, pi and half-pi values | [Special values](../lean/examples/trigonometric_special_values/) |
| Integer periods, all quadrants, negative angles and radicals | [Periodic values](../lean/examples/trigonometric_periodic_values/) |
| Arbitrary real arguments and tangent's domain | [Real output](../lean/examples/trigonometric_real_output/) |
| Symbolic sine-square plus cosine-square identity | [Pythagorean identity](../lean/examples/trigonometric_pythagorean/) |
| Tangent as a quotient, with its original nonzero premise | [Tangent quotient](../lean/examples/tangent_quotient/) |
| Named functions, nested calls, guarded tangent and scalar arithmetic | [Formula functions](../lean/examples/trigonometric_functions/) |

All six pairs pass strict source verification, independent-run regeneration and
Lean 4.31.0 with warnings treated as errors. Generated outputs are 3.0–58.4 KB.
The batch checks nine pairs including square-root and exp/log neighbors, with
43 exported theorem audits using only `propext`, `Classical.choice` and
`Quot.sound`. Six identical files reuse successful checks from the same batch;
three receive fresh final checks. The compiler regression passes **1173 tests**,
including rejection tests for missing or altered WD, wrong nonzero subjects,
changed period coefficients/values, complex arguments and tangent poles. Final
exact-angle renderer corrections are checked on the actual generated Lean.

This increment does not cover symbolic integer-period certificates, arbitrary
trigonometric identities or inequalities, inverse trigonometric functions,
reciprocal trigonometric functions or hyperbolic functions. Existing formula
function arity and scope boundaries still apply. Unsupported routes reject the
whole compilation artifact.

### Complex conjugation, coordinates and modulus, 2026-10-25

These source statements compile with their original execution evidence:

```litex
re(i) = 0
img(i) = 1
C_abs(3 + 4*i) = 5

forall z C:
    re(z) + img(z)*i = z
    conj(conj(z)) = z
    C_abs(z) >= 0
```

`ConjugateObj`, `RealPartObj`, `ImaginaryPartObj` and `ComplexAbsObj` own the
argument and its C-membership proof. Their fixed denotations wrap native complex
conjugation, real/imaginary projection and norm. Conjugation returns a complex
object; coordinates and modulus return real objects. No new model fields,
project axioms, AST fields, Runtime behavior or result fields are required.

Consumers replay exact closed calculations, intrinsic codomains, coordinate
reconstruction, conjugation involution and coordinate/modulus laws, conjugation
of sums/products, and modulus nonnegativity/multiplicativity. Exact modulus
calculations check the squared norm and the nonnegative root in Lean, including
rational coordinates. Formula functions retain the original Litex objects and
consume recorded substitutions and expansions.

| Checked use | Source and generated Lean |
| --- | --- |
| Exact coordinates, conjugate and modulus, including rational coordinates | [Complex values](../lean/examples/complex_observation_values/) |
| Output carriers for arbitrary complex inputs | [Codomains](../lean/examples/complex_observation_codomain/) |
| Reconstruction from real and imaginary parts | [Coordinate reconstruction](../lean/examples/complex_coordinate_reconstruction/) |
| Involution, coordinate/modulus preservation and addition/multiplication | [Conjugation laws](../lean/examples/complex_conjugation_laws/) |
| Nonnegative and multiplicative modulus | [Modulus laws](../lean/examples/complex_modulus_laws/) |
| Coordinate/modulus functions and nested conjugation calls | [Formula functions](../lean/examples/complex_observation_functions/) |

All six pairs pass strict source verification, independent-run regeneration and
Lean 4.31.0 with warnings treated as errors. New generated outputs are 3.0–21.7 KB.
The final batch covers nine pairs, including complex rotation, complex polynomial
and trigonometric-function neighbors. Four identical files reuse successful
checks from the same batch; five receive fresh checks. All 33 exported theorem
audits use only `propext`, `Classical.choice` and `Quot.sound`. The compiler
regression passes **1177 tests**. Five final focused tests cover the example
sources, missing/altered WD, changed calculation values, rejected set arguments
and a mismatched conjugation rule; these overlap the regression. Final numeric
rendering and the fractional-coordinate example are also checked on actual
generated Lean.

Constructor coverage does not imply every complex proof route is supported.
Modulus radical-value certificates, the general coordinate formula for modulus,
coordinate quotient rules, real-specific conjugation and natural-power rules,
and further complex inequality rules still need consumers. Existing formula
function arity and scope boundaries remain in place.

### Reciprocal and inverse trigonometric objects, 2026-10-25

`cot`, `sec`, `csc`, `arcsin`, `arccos`, `arctan` and `arccot` now have owned
Lean constructors. Each consumes its original argument WD and domain evidence:
arcsine/arccosine require `-1 <= x <= 1`; secant requires nonzero cosine;
cosecant/cotangent require nonzero sine. Arccotangent uses the existing source
principal interval `(0, pi)`, represented by `Real.pi / 2 - Real.arctan x`.

For `tan(arctan(x))` and `sec(arctan(x))`, the source WD omits an explicit
cosine-nonzero requirement. A proved Core law supplies this guard from the
owned arctangent. The corresponding sine law handles `cot(arccot(x))` and
`csc(arccot(x))`. Secant/cosecant retain the source's intrinsic nonzero-real
codomain, using the existing `SetSemantics` interface for `R*`.

These examples compile through the selected source rules:

```litex
forall x R:
    tan(arctan(x)) = x
    cot(arccot(x)) = x

have fn principal_sine(x R: -1 <= x, x <= 1) R = arcsin(x)
principal_sine(0) = 0
```

The constructor's lower bound uses the numeric value `-1`. A source citation
may instead refer to the owned negation of `1`; the compiler transports that
original bound through its checked numeric denotation. It does not assume the
two host representations are definitionally equal. No AST, result-producer,
Runtime or model-field changes were needed.

| Checked use | Source and generated Lean |
| --- | --- |
| Eight exact principal values | [Inverse values](../lean/examples/inverse_trigonometric_values/) |
| Four left inverses on their domains | [Left inverses](../lean/examples/inverse_trigonometric_left_inverses/) |
| Real codomains and guarded compositions | [Domains](../lean/examples/inverse_trigonometric_domains/) |
| Secant, cosecant and cotangent quotient definitions | [Quotient definitions](../lean/examples/reciprocal_trigonometric_definitions/) |
| Secant at zero/pi and cosecant at pi/2 | [Reciprocal values](../lean/examples/reciprocal_trigonometric_values/) |
| Bounded formula functions and nested calls | [Formula functions](../lean/examples/inverse_trigonometric_functions/) |

All six pairs pass strict source verification, actual CLI generation,
byte-identical independent regeneration and Lean 4.31.0 with warnings treated
as errors. Their generated files are 8.3–40.3 KB. The final batch includes three
existing trig, complex-function and exact-number examples: nine pairs pass,
with three unchanged checks reused from the same batch and six fresh checks.
All 46 exported theorem audits use only `propext`, `Classical.choice` and
`Quot.sound`. The compiler regression passes **1183 tests**, including five
new tests for source replay, missing/altered WD, boundary subjects, invalid
domains/poles and mismatched exact-value rules.

This increment does not consume the four right-inverse rules, such as
`arcsin(sin(x)) = x` on the principal interval. Cotangent periodic-value
certificates (including `cot(pi/4) = 1`), further reciprocal identities and
general trigonometric bound rules also remain unsupported. These routes reject
the compilation artifact; constructor coverage does not imply rule coverage.

## Compiler coverage baseline before phases 1–2, 2026-10-26

This records the dispatcher audit before the Fact expansion below. It counts
existing Litex features whose results the compiler could not yet consume at
that checkpoint. Keep these baseline counts separate from later deliveries.

| Layer | Baseline inventory | Missing compiler entrypoints |
| --- | ---: | ---: |
| Statement leaf forms | 52 | 4 |
| Object constructor leaves | 128 | 55 |
| Atomic fact variants | 74 | 47 lack proposition rendering |
| Explicit reserved builtin theorem IDs | 533 | 528 |
| Automatic equality builtin result variants | 233 | 140 lack dispatcher arms |
| Builtin strategy result variants | 140 | 95 lack dispatcher arms: 5 equality, 90 non-equality |

An entrypoint may still reject nested certificate variants, domains or scopes.
These counts use different units and must not be combined into a completion
percentage. The automatic non-equality inventory has 398 variant slots;
references in helper and source-position code are insufficient to establish
their support, so this audit does not assign them a completion count.

### Statements and scope restrictions

The four missing statement forms are algorithm definitions by cases, algorithm
definitions by induction, user strategy definitions, and `eval`. See the
[definition dispatcher](../src/compile_to_lean/compile_definition_stmt_result.rs)
and [statement dispatcher](../src/compile_to_lean/compile_stmt_result.rs).

`trust` and user `axiom` already enter through explicit assumptions. Replacement,
regularity, choice and Zorn have consumers. They are not missing statement forms.

Among forms with consumers, local template declarations, local piecewise
functions, local recursively defined functions and local functions selected
from unique existence remain rejected. The current object-template consumer
accepts a single `have ... = ...` body. Recursive functions accept the checked
unary natural-number zero/positive case shape with numeric return carrier;
nested recursive case bodies are rejected. See
[templates](../src/compile_to_lean/compile_template_stmt_result.rs),
[piecewise functions](../src/compile_to_lean/compile_have_fn_cases_result.rs),
[recursive functions](../src/compile_to_lean/compile_have_fn_by_induc_result.rs)
and [selected functions](../src/compile_to_lean/compile_have_fn_by_exist_result.rs).

### Objects without constructors

| Group | Count | Missing constructors |
| --- | ---: | --- |
| General folds | 2 | `reduce`, `finite_set_reduce` |
| Hyperbolic functions | 6 | `sinh`, `cosh`, `tanh`, `coth`, `sech`, `csch` |
| Set operations | 5 | Symmetric difference, family intersection, indexed union/intersection/Cartesian product |
| Analysis | 19 | Supremum/infimum; sequence, function and multivariable limits; limsup/liminf; derivatives and differential operators; Riemann integral |
| Matrices and finite-dimensional operations | 23 | Matrix set plus determinant, zero/identity matrix, transpose/adjoint, trace, add/subtract/scale/multiply/apply/power/inverse/rank, minor/cofactor/adjugate/diagonal, outer/inner product and Euclidean/Frobenius norms |

Analysis's 19 entries comprise 2 bounds, 6 limit constructors, 10 derivative
constructors and 1 integral constructor. The derivative entries are partial,
scalar differential, total differential, gradient, Jacobian, Hessian,
divergence, curl, Laplacian and derivative at a point. These are AST constructor
counts, rather than counts of mathematical theorems or all domain modes.

### Fact expressions and proof replay

All ten outer Fact shapes have consumers, including existence, unique
existence, disjunction, conjunction and quantified statements. Of the 74
atomic variants, 47 still lack proposition rendering:

- Six number-theory variants: prime, coprime and divisibility, with their negations.
- Nine set variants: superset, proper subset and proper superset with their
  negations, plus negated set/nonempty-set/finite-set predicates.
- Thirty-two analysis variants: real bounds/boundedness/accumulation, sequence
  analysis and limits/limsup/liminf, function limits, continuity, Lipschitz
  continuity, differentiability/derivatives, integrability/integrals and
  multivariable analysis, including their negations.

The renderer is [atomic_proposition](../src/compile_to_lean/names.rs); mapping
predicates are handled by an earlier guard and must not be counted as missing.

Three successful atomic search routes still reject unconditionally:
`ByTemplateMembership`, `ByKnownZeroRemainder` and `ByKnownStrategy`. Analysis
inference-result replay is also missing. See the
[atomic dispatcher](../src/compile_to_lean/compile_fact_stmt_result/compile_atomic_except_equality_result/compile_atomic_except_equality_result.rs)
and [inference consumers](../src/compile_to_lean/compile_compound_stores.rs).
An unsupported inferred fact is not silently promoted to a Lean assumption.

### Builtin theorem calls, rules and strategies

Only five explicit builtin theorem IDs currently have consumers:
`fn_set_member`, `set_builder_member`, `defined_set_member`,
`cart_member_from_coordinates` and `tuple_equal_from_coordinates`.
The other 528 reserved IDs need consumers. This does not count ordinary user
theorems or automatic rules: those have separate replay paths.

The 140 missing automatic equality dispatcher arms include analysis,
hyperbolic functions, symmetric difference, general folds, several finite
collection identities, logarithm/power identities, complex coordinate rules
and all four inverse-trigonometric right inverses. Some arms that do exist
also have unsupported nested certificates: for example, `cot` construction is
supported but `cot(pi/4) = 1` selects the unsupported periodic-value route.
The same mathematical equality may succeed through another supported route.

The five missing equality strategies are `ComplexWithNonzeroPremises`,
`CosZeroIntegerOffset`, `ExtremumEquality`,
`FiniteSetProductPointwiseEquality` and `ModCongruence`. The 90 missing
non-equality strategies include additional numeric carrier closure,
sign-sensitive inequalities, finite/nonempty set propagation, function-space
and set-builder membership, pointwise continuity/derivatives and multivariable
analysis. A strategy being missing does not mean every fact in that domain
fails: compilation follows the particular certificate returned by verification.

A practical next batch is to finish more proof routes for existing objects
and facts, followed by the missing set/number-theory expressions and folds.
Analysis and matrix support each require their own constructors, predicates,
WD consumers and theorem adapters; they should be delivered as separate batches.

## Approved Fact and Obj implementation order, 2026-10-26

The inventory table above is the recorded pre-implementation baseline. The
following table records the approved order. Delivered checkpoints appear
below; later phases are not counted as coverage before their checks finish.

| Phase | Scope | Acceptance target |
| --- | --- | --- |
| 1. Basic set facts | Nine missing atomic variants: superset, proper subset/superset and their negations; negated sethood, nonemptiness and finiteness | Predicates in assumptions, conclusions, named theorems and citations; selected definition/basic proof routes |
| 2. Number-theory facts | Prime, coprime, divisibility and their negations: six variants | Original numeric domains and WD, closed examples, generic assumptions and theorem references |
| 3. Set objects | Symmetric difference, family intersection, indexed union/intersection/Cartesian product: five constructors | Construction, membership proofs and later citations |
| 4. General folds | `reduce`, `finite_set_reduce` | Function arguments, initial values, call WD and basic unfolding |
| 5. Hyperbolic objects | `sinh`, `cosh`, `tanh`, `coth`, `sech`, `csch` | Constructors, domains, basic values and defining identities |
| 6. Matrix objects | Twenty-three constructors, delivered in smaller batches | Matrix sets/basic operations, then determinant/inverse/rank, then inner products/norms |
| 7. Analysis facts and objects | Thirty-two atomic variants and nineteen constructors | Bounds/suprema, sequences, function limits/continuity, derivatives/integrals, then multivariable analysis |

Each batch supplies semantic definitions and proved bridges in `lean/Litex.lean`,
consumes the original WD and selected result evidence, and adds real generated
source/Lean pairs. Add only the builtin rules and explicit theorem consumers
needed by the batch's accepted scope. Rendering a predicate alone is not proof
coverage. Run focused checks while implementing and the compiler regression
once at the coherent batch checkpoint. Preserve the approved result-driven
architecture and source FactId citations.

## Phases 1–2: set and number-theory facts, 2026-10-26

The compiler now renders all fifteen atomic variants in these two phases:
superset, proper subset/superset, prime, coprime and divisibility, each with
its negation, plus negated sethood, nonemptiness and finiteness. Atomic
proposition coverage increases from 27/74 to 42/74; the remaining 32 variants
are analysis predicates. This count describes proposition forms, not all
possible proofs of those propositions.

`Litex.Superset A B` means `Litex.Subset B A`. Proper inclusion combines
inclusion with inequality of semantic denotations. The number-theory
predicates are defined using `Nat.Prime`, `Nat.Coprime` and integer
divisibility. They retain the source domains: natural numbers for prime and
coprime, and an integer dividend with a nonzero integer divisor for `dvd`.
In particular, `$dvd(a,b)` means **b divides a**. The proved bridges
`prime_iff_of_denote`, `coprime_iff_of_denote` and `dvd_iff_of_denote` connect
these predicates to ordinary Mathlib propositions. No new model axioms or
runtime/result fields are required.

Supported proof routes in this batch are:

- Direct fact citations, named theorem use, and transport along the recorded
  argument equalities for the fifteen new predicates.
- Superset definition, reflexivity and standard-number-set inclusion;
  proper inclusion from its definition, with the resulting subset and
  inequality facts emitted under their original IDs.
- Finite-list inclusion from the recorded member proofs, and unequal list
  cardinalities from the existing certified set constructors.
- Empty-set noninhabitation and infinitude of `N`.
- Closed primality/coprimality computation, including negative results;
  divisibility from a recorded zero-remainder proof, including arbitrary
  integer parameters and nonzero-divisor WD.

The generated examples are:

| Example | Source | Generated Lean |
| --- | --- | --- |
| Nine set predicate interfaces | [Litex](../lean/examples/set_predicate_contexts/statement.lit) | [Lean](../lean/examples/set_predicate_contexts/statement.lean) |
| Proper inclusion, derived citations and named theorem use | [Litex](../lean/examples/proper_set_relations/statement.lit) | [Lean](../lean/examples/proper_set_relations/statement.lean) |
| Empty set and infinite natural numbers | [Litex](../lean/examples/negative_set_values/statement.lit) | [Lean](../lean/examples/negative_set_values/statement.lean) |
| Six number-theory interfaces and equality transport | [Litex](../lean/examples/number_theory_predicate_contexts/statement.lit) | [Lean](../lean/examples/number_theory_predicate_contexts/statement.lean) |
| Prime and coprime values, with named theorem reuse | [Litex](../lean/examples/number_theory_values/statement.lit) | [Lean](../lean/examples/number_theory_values/statement.lean) |
| Zero remainder implies divisibility | [Litex](../lean/examples/integer_divisibility/statement.lit) | [Lean](../lean/examples/integer_divisibility/statement.lean) |

The interface examples preserve assumptions and conclusions. In particular,
the `not $is_set(A)` example assumes an inconsistent premise; it does not
claim that such an object exists.

Other selected proof routes remain separate work: number-theory `by def`
expansions and their inferred consequences, additional set rules, and
standard-set infinitude beyond `N`. A source proof selecting one of those
unsupported routes is rejected. Phases 3–7 remain queued.

Validation: `cargo test --lib compile_to_lean::tests` passed all 843 tests,
including six new tests for these predicates, their examples and invalid
evidence. All six source files passed strict execution, generated repeatable
Lean output, and passed Lean 4.31.0 with Mathlib
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. The 38 generated theorems were
audited with `#print axioms`; the only dependencies were `propext`,
`Classical.choice` and `Quot.sound`. Negative checks reject false claims,
missing domains, altered computation results and a remainder certificate
with the wrong divisor. These are local checks, not a CI claim.


## Phase 3: set constructors, 2026-10-26

This batch connects five existing source constructors: `set_diff(A,B)`,
`family_intersect(F)`, `index_union(I,X,A)`, `index_intersect(I,X,A)` and
`index_cart(I,S,g)`. Objects retain their child objects and WD evidence.
The compiler validates and consumes the original results and fact citations.

The family-intersection domain changed with the maintainer's approval:
`family_intersect(F)` now requires `$is_nonempty_set(F)` during WD. The
existing `requirement_fact_verified` field carries that proof; AST and result
shapes are unchanged. Empty families and generic families without nonempty
evidence fail WD. A nonempty family can have an empty intersection: `{{}}`
is a valid family. The dedicated source gallery and both manuals reflect
this restriction.

Lean constructs the family intersection by separation inside the family
union. Nonemptiness supplies a member set when proving the ordinary
intersection membership characterization. This uses existing SetSemantics
and the optional IndexedUnionSemantics, with their existing ZF model; no
new axiom or model-class field is introduced.

The indexed constructors preserve their source domains. Union/intersection
require a nonempty index I, an ambient set X, and `A in fn(k I) power_set(X)`.
The indexed product requires nonempty I and S and `g in fn(k I) S`; membership
uses the captured function membership and choice-function certificate.

Supported selected proof routes are:

- The four symmetric-difference membership/nonmembership cases, the defining
  union of two differences, and `set_diff(A,A) = {}`.
- Indexed-union membership from the recorded index membership and fiber proof.
- The existing two-argument explicit theorems `family_intersect_member`,
  `index_intersect_member` and `index_cart_member`.
- WD, sethood, ordinary references and structural theorem instantiation for
  these constructors. The family-intersection example includes a named
  theorem and its later application to a singleton family.

`forallMembersOfRepresentations` bridges a source universal premise to
semantic membership using a one-point host carrier. Its proved construction
works even when the premise's host universe differs from the model's
universe; generated source parameters keep their existing representations.

| Example | Source | Generated Lean |
| --- | --- | --- |
| Four symmetric-difference membership cases | [Litex](../lean/examples/symmetric_difference_membership/statement.lit) | [Lean](../lean/examples/symmetric_difference_membership/statement.lean) |
| Symmetric-difference identities | [Litex](../lean/examples/symmetric_difference_identities/statement.lit) | [Lean](../lean/examples/symmetric_difference_identities/statement.lean) |
| Indexed-union membership | [Litex](../lean/examples/indexed_union_member/statement.lit) | [Lean](../lean/examples/indexed_union_member/statement.lean) |
| Indexed-intersection membership | [Litex](../lean/examples/indexed_intersection_member/statement.lit) | [Lean](../lean/examples/indexed_intersection_member/statement.lean) |
| Indexed-product membership | [Litex](../lean/examples/indexed_product_member/statement.lit) | [Lean](../lean/examples/indexed_product_member/statement.lean) |
| Nonempty-family intersection and theorem reuse | [Litex](../lean/examples/family_intersection_member/statement.lit) | [Lean](../lean/examples/family_intersection_member/statement.lean) |

Remaining routes include `family_intersect_member_facts`, general indexed-set
algebra, symmetric-difference finite evaluation and further equality rules.
Unsupported selected routes still reject compilation. Phases 4–7 remain
queued.

Validation: all six strict source/generated pairs passed Lean 4.31.0 with the
same pinned Mathlib revision as phases 1–2. Regeneration was byte-identical;
13 generated theorems passed axiom audits with only `propext`,
`Classical.choice` and `Quot.sound`. Files range from 3,405 to 20,693 bytes.
Seven affected source checks passed, including expected WD rejections and the
existing family-intersection gallery. All 847 compiler tests and the dedicated
Runtime WD/failed-scope regression passed. The rebuilt release CLI reproduced
all six checked Lean files byte for byte.


### Known power-set closure replay, 2026-10-26

The four recorded KnownSpecialProperty routes UnionInPowerSet,
IntersectInPowerSetFromLeft/Right and SetMinusInPowerSet replay their original
membership citations through inPowerSet_iff and the existing proved subset
laws. No new Lean axiom or semantic primitive is added. The consumer validates
the source operator, both union operands and each child's exact power-set
carrier; altered operands/carriers fail closed. The
[mathematical source](../lean/examples/power_set_operation_closure/statement.lit)
and its [generated target](../lean/examples/power_set_operation_closure/statement.lean)
cover all four routes plus equality transport. Five actual Lean theorems pass
Lean4.31.0 with pinned Mathlib, with only the permitted standard axioms. This
does not add compilation support for the finite probability structure or its
quantified probability laws.


## Phase 4: general folds, 2026-10-26

Both `reduce(a,b,f,op,seed)` and `finite_set_reduce(S,f,op,seed)` now have
Lean object representations. They keep Litex function objects and membership
facts: the return carrier can be an arbitrary set E. The binary operation
must map E × E to E, with no additional explicit input conditions.

`reduce` is a left fold over ascending, inclusive integer indices. A finite
set fold uses a finite enumeration; its result is independent of that
ordering by the captured commutative and associative laws. The permutation
proof is proved in `Litex.lean`, without a new semantics axiom or class.

The original WD results now retain both selected function signatures as
`operation_signature_selection` and `iterand_signature_selection`, including
existing fact citations. Detailed JSON exposes these two fields. Runtime
ownership and the AST are unchanged. A local WD repair also checks the
ordered iterand's domain at every index: the old acceptance of
`reduce(1,2,fn(k {1}) Z{k},fn(a,b Z) Z{a+b},0)` is rejected. Empty intervals
make no calls and remain valid with restricted or guarded iterands.

The checked routes are:

- Generic output membership, empty-fold identities, and later references.
- Ordered index domains N, Z, Q, R and C; empty intervals with arbitrary
  domains. Nonempty guarded intervals consume either each recorded concrete
  condition or the original interval-wide universal proof.
- Finite-set domain coverage, each guard in a finite enumeration, and a
  universal guard over an arbitrary finite set. Empty sets need no guard
  instances.
- Ordered exact calculation, replaying every recorded unary and binary call,
  its WD, function body and intermediate value.
- The last-step rule for arbitrary integer endpoints, and the explicit
  `finite_set_reduce_singleton` theorem.

| Example | Source and generated Lean |
| --- | --- |
| Arbitrary return set | [Ordered](../lean/examples/ordered_fold_carrier/), [finite](../lean/examples/finite_fold_carrier/) |
| Empty identities and restricted domains | [Empty folds](../lean/examples/fold_empty/), [index domains](../lean/examples/fold_domains/) |
| Ordered subtraction calculation | [Calculation](../lean/examples/ordered_subtraction_fold/) |
| Singleton theorem and last-step expansion | [Singleton](../lean/examples/finite_fold_singleton/), [last step](../lean/examples/ordered_fold_last_step/) |
| Guarded symbolic and concrete intervals | [Symbolic](../lean/examples/ordered_fold_guarded/), [concrete](../lean/examples/ordered_fold_guarded_literal/) |
| Guarded arbitrary and enumerated finite sets | [Arbitrary](../lean/examples/finite_fold_guarded/), [enumerated and empty](../lean/examples/finite_fold_guarded_literal/) |

All eleven pairs passed strict source verification, byte-identical fresh
regeneration and Lean 4.31.0 with the pinned Mathlib revision above. The
fourteen exported theorems use only `propext`, `Classical.choice` and
`Quot.sound`. The compiler regression passed 862 tests at this checkpoint;
focused controls also reject missing or reordered guards, altered calculation
steps and a changed last-step endpoint.

Still outside this increment: nonempty ordered folds over other index sets,
the specialized positive-real numeric-signature bridge, guarded binary
operations, multi-element finite-fold calculation, and further fold BT rules.
The two constructors are available through the routes above; this is not a
claim that every native fold proof route compiles.


## Phase 5: real hyperbolic functions, 2026-10-26

`sinh`, `cosh`, `tanh`, `coth`, `sech` and `csch` retain their Litex object
representations and original WD. All inputs are real; `coth` and `csch` also
consume the recorded input-nonzero proof. Their intrinsic codomains remain
R, R+, or R* as specified by the native language.

The compiler replays all 28 variants of the existing hyperbolic equality-rule
enum: six definitions, six parity laws, reciprocal identities, the square
identities, exponential connections, addition and double-angle formulas.
It also supports the recorded nonzero rules, zero values, function-body
normalization and later fact references. Each selected rule validates its
source subjects before citing the corresponding proved Core law.

| Example | Source and generated Lean |
| --- | --- |
| All six domains and codomains | [Domains](../lean/examples/hyperbolic_domains/) |
| Values at zero | [Zero values](../lean/examples/hyperbolic_zero_values/) |
| Definitions through exp and quotients | [Definitions](../lean/examples/hyperbolic_definitions/) |
| Odd and even functions | [Parity](../lean/examples/hyperbolic_parity/) |
| Nonzero facts and guarded arguments | [Nonzero](../lean/examples/hyperbolic_nonzero/) |
| A formula function using sinh and cosh | [Function](../lean/examples/hyperbolic_function/) |
| Addition, double-angle and square identities | [Identities](../lean/examples/hyperbolic_identities/) |

All seven pairs passed strict source verification, independent byte-identical
regeneration and Lean 4.31.0 with the pinned Mathlib revision. The 18 exported
theorems use only `propext`, `Classical.choice` and `Quot.sound`. All 868 compiler
tests passed at this checkpoint. Focused controls reject missing or altered
nonzero WD, a wrong rule tag and a changed equality conclusion.

This increment does not add new Litex syntax, Runtime state, result fields or
proof search. General hyperbolic inequalities, calculus, complex arguments and
additional explicit `by thm` adapters are outside this checked slice.


## Phase 6a: matrix spaces and zero matrices, 2026-10-26

`matrix(S,m,n)` is represented as the existing finite two-argument function
space. S remains an arbitrary source set; m and n remain source objects with
natural-membership evidence, including zero. Indices run from 1 through each
dimension. Matrix membership expands to the original recorded function
signature, with its stored fact IDs and any carrier-equality citations.

The checked slice includes matrix-space formation and its defining equality,
generic coordinate membership, known or literal functions with the exact input
domain, and matrix-space aliases. `zero_matrix(m,n)` has an owned representation
with dimension WD. Its real/complex membership, constant-function definition,
coordinate value, real-valued coordinates and aliases compile through their
original result variants.

| Example | Source and generated Lean |
| --- | --- |
| Matrix spaces and function-space equality | [Spaces](../lean/examples/matrix_spaces/) |
| Coordinates over an arbitrary set S | [Coordinates](../lean/examples/matrix_coordinates/) |
| Functions as matrices; a zero dimension | [Membership](../lean/examples/matrix_membership/) |
| A named rectangular matrix space | [Alias](../lean/examples/matrix_alias/) |
| Zero matrices and coordinate values | [Zero matrix](../lean/examples/zero_matrix/) |
| Constant-function definition and an object alias | [Definition](../lean/examples/zero_matrix_definition/) |
| Real-valued components | [Return carrier](../lean/examples/zero_matrix_return/) |

The seven new pairs and three affected sequence/fold/composition pairs passed
strict source verification, byte-identical regeneration and actual Lean4.31.0
checking. Their 32 exported theorems use only `propext`, `Classical.choice` and
`Quot.sound`. All 873 compiler tests passed. Mutation controls cover missing or
reordered dimension WD, a wrong signature domain, an altered callable body
and a changed component-reduction endpoint.

This uses the existing `FunctionSemantics` interface, with no new model axiom,
Runtime state or result field. The shared call compiler now makes the just-
checked argument-domain constructors visible before packing the input; proving
input membership no longer reconstructs an unrelated output carrier. Other
matrix operators and broader residual-evaluation routes are subsequent batches.


## Phase 6b: transposition, 2026-10-26

Delivered `transpose(A,m,n)` with its original natural dimensions and complex
matrix membership WD. The representation stores the original matrix and its
shape; its graph reads the swapped coordinate. Captured real-input evidence
preserves the real output bound. No Runtime or result-shape change was needed.

Examples:

- [`matrix_transpose`](../lean/examples/matrix_transpose/statement.lit): complex matrix membership.
- [`matrix_transpose_coordinates`](../lean/examples/matrix_transpose_coordinates/statement.lit): `transpose(A,m,n)(row,col) = A(col,row)`.
- [`matrix_transpose_real`](../lean/examples/matrix_transpose_real/statement.lit): real matrix membership and real coordinate return.
- [`matrix_transpose_definition`](../lean/examples/matrix_transpose_definition/statement.lit): the complete formula function, for both R and C.

The compiler validates the selected signature, swapped binder IDs, original
input membership and component substitution before invoking the corresponding
Core law. Function definitions use proved graph extensionality even when the
source formula's real return bound differs from the constructor's complex bound.
Each matrix call binds its constructor once and projects its interface; the
real-transpose pair decreased from 226,121 to 83,977 generated bytes.

Acceptance: all four new pairs and six affected existing pairs passed strict
source execution, independent byte-identical generation and actual Lean
checking. All 29 exported theorems passed the standard-axiom audit. The focused
matrix module passed eight tests, including corrupt WD, body, input premise and
substitution rejections; `cargo test --lib compile_to_lean::` passed 1,222 tests.
Local receipts: `phase6b-final`, `phase6b-unit2`, `phase6b-compiler-regression`.

Still unsupported here: nested native component reduction, real-returned-function
carrier evidence, and the remaining matrix constructors. The implementation does
not introduce an ordinary Mathlib Matrix adapter.


## Phase 6c: nested matrix components and theorem calls, 2026-10-26

The compiler now consumes `MatrixComponentReduction::NativeApplication` in
recorded order, including each intermediate call's original WD and exact binder
substitution. New pairs are
[`matrix_transpose_twice`](../lean/examples/matrix_transpose_twice/statement.lit),
[`matrix_transpose_zero`](../lean/examples/matrix_transpose_zero/statement.lit), and
[`matrix_transpose_theorem`](../lean/examples/matrix_transpose_theorem/statement.lit).
They cover real/complex coordinates after two transposes, transposed zero entries,
and a named coordinate theorem instantiated at a concrete zero matrix.
The theorem-call validator now substitutes original IDs through matrix objects
and integer interval endpoints. Runtime and result shapes are unchanged.

Six new/affected pairs passed strict source execution, byte-identical independent
generation, actual Lean checking and 13 theorem audits. Nine focused matrix tests
and 1,223 compiler-module tests passed. Receipts: `phase6c-final`, `phase6c-unit2`,
`phase6c-compiler-regression`. The complex double-transpose coordinate proof alone
is 24,055 bytes; the pair including its real variant is 159,466 bytes.

The separate assertion that a double transpose belongs to a real matrix space
currently selects an unsupported builtin strategy. That route remains deferred;
its source probe is retained locally rather than listed as a delivered pair.


## Phase 6d: conjugate transpose and complete involutions, 2026-10-26

`conjugate_transpose(A,m,n)` now replays the original complex matrix WD,
coordinate swap, conjugation and captured real-input evidence. The Core graph
uses the same owned complex conjugation operation as ordinary Litex objects.
`ConjugateArgument` reduction composes the recorded inner expansion with
congruence. No Runtime, AST or result-shape changes were made.

New pairs:

- [`matrix_conjugate_transpose`](../lean/examples/matrix_conjugate_transpose/statement.lit)
- [`matrix_conjugate_transpose_coordinates`](../lean/examples/matrix_conjugate_transpose_coordinates/statement.lit)
- [`matrix_conjugate_transpose_real`](../lean/examples/matrix_conjugate_transpose_real/statement.lit)
- [`matrix_conjugate_transpose_definition`](../lean/examples/matrix_conjugate_transpose_definition/statement.lit)
- [`matrix_conjugate_transpose_nested`](../lean/examples/matrix_conjugate_transpose_nested/statement.lit)
- [`matrix_conjugate_transpose_involution`](../lean/examples/matrix_conjugate_transpose_involution/statement.lit)
- [`matrix_transpose_involution`](../lean/examples/matrix_transpose_involution/statement.lit)

The last two are complete named theorems proved through the source
`by fn_extension` flow. That consumer now keeps the recorded matrix carrier as
the actual citation-path endpoint, then applies `matrixSet_eq_fnSet`. Conjugate
involution cites Mathlib's `star_star` directly, including when its argument is
a locally named matrix call. Equality-path errors now display the three actual
endpoints to make producer/consumer mismatches diagnosable.

Acceptance: 11 new/affected pairs, independent byte-identical generation,
23 standard-axiom audits. The full compiler-module checkpoint passed 1,225 tests;
the final conjugation fix passed all five complex-observation tests and actual
Lean checks for both the matrix involution and existing conjugation laws.
Eleven focused matrix tests include rejection of missing conjugation and
changed conjugate-reduction endpoints. Receipt `phase6d-final` reuses only
identical previously checked bytes with unchanged Core/toolchain; changed files
were checked afresh. Remaining matrix constructors and RealReturnedFunction
carrier evidence are still outside this increment.


## Phase 6e: identity matrices and finite intersections, 2026-10-26

`identity_matrix(n)` keeps the native definition: entry `(row,col)` is
`finite_set_size(intersect({row},{col}))`. Its constructor consumes the original
natural-order WD. Core proves the diagonal/off-diagonal cardinalities; closed
entry compilation validates the captured exact-evaluation values and rejects
additional uncaptured calculation stages. `IntersectFiniteFromBoth` now consumes
both original finite-set premises. Parent-checked matrix beta uses the existing
call WD; identical expanded endpoints use reflexivity without a second object
constructor. No Runtime, AST or result-shape change was needed.

New source/generated pairs:

- [`identity_matrix`](../lean/examples/identity_matrix/statement.lit): real/complex matrix membership, including order zero.
- [`identity_matrix_coordinates`](../lean/examples/identity_matrix_coordinates/statement.lit): the general singleton-intersection formula.
- [`identity_matrix_values`](../lean/examples/identity_matrix_values/statement.lit): diagonal `1` and off-diagonal `0`.
- [`identity_matrix_formula`](../lean/examples/identity_matrix_formula/statement.lit): a named whole-function theorem proved by `fn_extension`.
- [`finite_intersection`](../lean/examples/finite_intersection/statement.lit): intersection of two finite sets.

Eight new/affected pairs passed strict source execution, independent identical
generation and real Lean checks; 14 exported theorems passed the standard-axiom
audit. The compiler-module checkpoint passed 1,230 tests, including malformed
order, body, exact-evaluation and finite-premise rejection. Receipts:
`phase6e-final`, `phase6e-compiler-regression`. The function-formula example is
234,312 bytes; the other new pairs are 1,477–17,255 bytes. Direct automatic
whole-function identity expansion remains a native proof-search boundary;
the delivered example uses its successful explicit extensionality route.


## Phase 6f: pointwise matrix addition and subtraction, 2026-10-26

`matrix_add(A,B,m,n)` and `matrix_sub(A,B,m,n)` now consume the original
matrix and dimension WD, exact two-parameter body and real-operand certificates.
The Core graph applies owned scalar addition/subtraction to corresponding
entries. Matrix residuals also replay the captured left/right checked beta
steps before citing their recorded scalar equality. Runtime and result shapes
are unchanged.

New pairs: [`matrix_addition`](../lean/examples/matrix_addition/statement.lit),
[`matrix_subtraction`](../lean/examples/matrix_subtraction/statement.lit),
[`matrix_entrywise_coordinates`](../lean/examples/matrix_entrywise_coordinates/statement.lit),
[`matrix_entrywise_real`](../lean/examples/matrix_entrywise_real/statement.lit),
[`matrix_entrywise_definition`](../lean/examples/matrix_entrywise_definition/statement.lit),
and [`matrix_addition_commutative`](../lean/examples/matrix_addition_commutative/statement.lit).
The last is a named whole-matrix theorem proved by source `fn_extension`.

The batch passed 10 new/affected pairs and 17 theorem audits. The compiler-module
checkpoint passed 1,232 tests. A subsequent signature-reference simplification
passed four affected pairs and reduced the real-coordinate pair from 191,484
to 184,302 bytes. It reuses the captured matrix signature and binds it once.
Receipts: `phase6f-final`, `phase6f-compiler-regression`,
`phase6f-signature-sharing`. Additional exact matrix evaluations, matrix
multiplication and other matrix constructors remain separate work.


## Phase 6g: matrix scalar multiplication, 2026-10-26

`matrix_scale(z,A,m,n)` is now a Core graph with the original scalar, matrix,
rows and columns. Constructor WD consumes `z in C`, both natural dimensions
and the complete complex matrix domain, in the native result order. Real
return evidence separately checks the matrix and scalar real-membership
results. Coordinates and full formula equality reuse the checked matrix beta
consumer. No Runtime, AST or result-shape change was needed.

New pairs: [`matrix_scale`](../lean/examples/matrix_scale/statement.lit),
[`matrix_scale_coordinates`](../lean/examples/matrix_scale_coordinates/statement.lit),
[`matrix_scale_definition`](../lean/examples/matrix_scale_definition/statement.lit),
and [`matrix_scale_one`](../lean/examples/matrix_scale_one/statement.lit).
They cover complex/real domains, pointwise multiplication and the complete
named theorem that multiplication by one preserves a matrix.

Six new/affected pairs passed strict source, independent identical generation,
real Lean checking and ten theorem audits (`phase6g-final`). The focused matrix
suite passed 18 tests, including wrong scalar-domain order and changed scalar
factor rejection (`phase6g-unit1`). The preceding compiler-wide checkpoint
remains `phase6f-compiler-regression`; no new full-suite claim is made here.


## Phase 6h: outer products and finite-vector carriers, 2026-10-26

`outer_product(a,b,m,n)` now keeps both source vector functions and their
complete finite domains. The graph multiplies `a(row)` by `b(col)`, with the
original complex WD and separate real-vector membership evidence. The compiler
also replays the existing function-set-membership strategy and the restricted
literal-tuple carrier certificate. Empty-guard function proofs no longer emit
a simplification step that has nothing to simplify. Runtime and result shapes
are unchanged.

New pairs:

- [`matrix_outer_product`](../lean/examples/matrix_outer_product/statement.lit): real and complex matrix membership.
- [`matrix_outer_coordinates`](../lean/examples/matrix_outer_coordinates/statement.lit): the coordinate formula.
- [`matrix_outer_definition`](../lean/examples/matrix_outer_definition/statement.lit): whole-function equality.
- [`matrix_outer_transpose`](../lean/examples/matrix_outer_transpose/statement.lit): transpose exchanges the two vectors.
- [`finite_sequence_carrier_widening`](../lean/examples/finite_sequence_carrier_widening/statement.lit): real vectors are complex vectors.
- [`finite_tuple_function_carrier`](../lean/examples/finite_tuple_function_carrier/statement.lit): literal tuples and aliases as finite functions.
- [`matrix_outer_literal`](../lean/examples/matrix_outer_literal/statement.lit): outer product of literal real vectors.
- [`matrix_transpose_twice_real`](../lean/examples/matrix_transpose_twice_real/statement.lit): the earlier real-domain blocker is resolved.

Eleven new/affected pairs passed strict source execution, independent identical
generation and actual Lean checking; 17 exported theorems passed the standard
axiom audit (`phase6h-final`). Twenty existing matrix tests passed, followed by
the corrected tuple-certificate rejection test (`phase6h-tuple-test2`). The last
compiler-wide checkpoint is still phase6f; the next batch will refresh it.


## Phase 6i: diagonal matrices, 2026-10-26

`diagonal_matrix(v,n)` now compiles with its original natural order and full
finite-vector domain. The entry definition remains
`finite_set_size(intersect({row},{col})) * v(row)`. Core reuses the proved
identity-entry cardinality and vector-call membership laws. The constructor,
real/complex membership, coordinates and full function theorem consume existing
results; Runtime, AST and result shapes are unchanged.

New pairs: [`matrix_diagonal`](../lean/examples/matrix_diagonal/statement.lit),
[`matrix_diagonal_coordinates`](../lean/examples/matrix_diagonal_coordinates/statement.lit),
[`matrix_diagonal_formula`](../lean/examples/matrix_diagonal_formula/statement.lit),
and [`matrix_diagonal_literal`](../lean/examples/matrix_diagonal_literal/statement.lit).
The complete formula theorem uses the source's successful `fn_extension` route;
automatic discovery of that whole equality is not claimed.

All four pairs passed strict source execution, independent identical generation
and real Lean checking, with six theorem audits (`phase6i-first`). The compiler
module checkpoint passed 1,239 tests, including altered/missing diagonal WD,
changed delta body and the phase6h tuple-certificate negatives
(`phase6i-compiler-regression`). This checkpoint also covers phases6g–6h.


## Phase 6j: returned matrices and finite vectors, 2026-10-26

A function returning `matrix(S,m,n)` or `finite_seq(S,n)` can now be followed
by a coordinate call. The compiler reads the original two call stages, outer
guards and index memberships; it does not invent a normalized source function
signature. Carrier equality follows the captured path to its actual wrapper,
then uses the proved wrapper-to-function-space law. Transpose and conjugate
transpose also consume `RealReturnedFunction` evidence.

New pairs: [`returned_matrix_coordinates`](../lean/examples/returned_matrix_coordinates/statement.lit),
[`returned_matrix_guarded`](../lean/examples/returned_matrix_guarded/statement.lit),
[`returned_finite_sequence_values`](../lean/examples/returned_finite_sequence_values/statement.lit),
[`returned_matrix_transpose`](../lean/examples/returned_matrix_transpose/statement.lit),
and [`returned_matrix_function_transpose`](../lean/examples/returned_matrix_function_transpose/statement.lit).
The coordinate examples include arbitrary dimensions, nonzero outer guards and
real-to-complex return inclusion. This increment supports one outer call followed
by one matrix/vector coordinate call; arbitrary deeper wrapper chains are not
claimed.

Eight new/affected pairs passed strict source, independent identical generation,
actual Lean and 13 theorem audits (`phase6j-final`). Ten focused returned-function
tests passed, including missing/swapped coordinates, altered real-return carrier
and absent applicability evidence (`phase6j-unit3`). The last compiler-wide
checkpoint is phase6i. Runtime, AST and result shapes are unchanged.


## Phase 6k: finite aggregation on explicit domains, 2026-10-26

`finite_set_sum` and `finite_set_product` now accept iterands defined on a
bounded interval or an arbitrary explicit set. The original finite-set proof,
subset relation, return inclusion and selected function signature remain in
the constructor's WD. The generic representation shares the existing numerical
fold meaning. The compiler also replays intrinsic `range`/`closed_range`
finiteness and exact aggregate calls through their generic domain proof.

New pairs: [`bounded_finite_aggregate_closure`](../lean/examples/bounded_finite_aggregate_closure/statement.lit),
[`general_finite_aggregate_closure`](../lean/examples/general_finite_aggregate_closure/statement.lit),
[`bounded_finite_aggregate_values`](../lean/examples/bounded_finite_aggregate_values/statement.lit),
and [`integer_ranges_finite`](../lean/examples/integer_ranges_finite/statement.lit).
Six new/affected pairs and 12 theorem audits passed actual Lean
(`phase6k-second`); 13 aggregate tests passed, including altered bounded-domain
signature rejection (`phase6k-unit`). No Runtime/AST/result change. Additional
iterand guards and non-list exact enumeration remain outside this increment.


## Phase 6l: matrix trace, 2026-10-26

`trace(A,n)` now retains the original square-matrix WD and compiles its complex
and real membership proofs and diagonal-sum definition. Finite sums/products
also consume recorded alpha equality when only a bound parameter name changes;
a changed iterand is rejected. No Runtime, AST or result change.

New pairs: [`matrix_trace`](../lean/examples/matrix_trace/statement.lit),
[`matrix_trace_definition`](../lean/examples/matrix_trace_definition/statement.lit),
and [`finite_aggregate_bound_names`](../lean/examples/finite_aggregate_bound_names/statement.lit).
All three passed strict source, independent identical generation and real Lean;
five exported theorems passed the standard axiom audit (`phase6l-second`).
The compiler module passed 1,247 tests (`phase6l-compiler-regression`), covering
phases6j–6l and altered trace domain/body certificates. Numerical trace evaluation
over integer intervals is not included.


## Phases 6m–6o: matrix products, vector application and inner products, 2026-10-26

`matrix_mul(A,B,m,k,n)` and `matrix_apply(A,v,m,n)` now compile their
original compatible-dimension and operand-membership evidence. Their coordinate
and whole-function definitions use the existing finite sum over the shared
index range. Complex and real membership and later coordinate calls preserve
the source's scalar carrier. Finite aggregates inside function bodies reuse the
source's lexical parameter IDs and original function/aggregate WD.

`inner_product(v,w,n)` means the finite sum of `conj(v(k)) * w(k)`; the
left operand is conjugated. Core proves complex closure and real closure for
real vectors, and the compiler consumes the original scalar-definition result.
These increments add no Runtime, AST or result fields and no model axioms.

| Example | Checked source and generated Lean |
| --- | --- |
| Matrix multiplication over R/C | [Source](../lean/examples/matrix_multiplication/statement.lit) · [Lean](../lean/examples/matrix_multiplication/statement.lean) |
| Product coordinates | [Source](../lean/examples/matrix_multiplication_coordinates/statement.lit) · [Lean](../lean/examples/matrix_multiplication_coordinates/statement.lean) |
| Whole matrix-product formula | [Source](../lean/examples/matrix_multiplication_definition/statement.lit) · [Lean](../lean/examples/matrix_multiplication_definition/statement.lean) |
| Matrix applied to a vector | [Source](../lean/examples/matrix_vector_application/statement.lit) · [Lean](../lean/examples/matrix_vector_application/statement.lean) |
| Vector coordinates | [Source](../lean/examples/matrix_vector_coordinates/statement.lit) · [Lean](../lean/examples/matrix_vector_coordinates/statement.lean) |
| Whole matrix-vector formula | [Source](../lean/examples/matrix_vector_definition/statement.lit) · [Lean](../lean/examples/matrix_vector_definition/statement.lean) |
| Finite inner-product carriers | [Source](../lean/examples/finite_inner_product/statement.lit) · [Lean](../lean/examples/finite_inner_product/statement.lean) |
| Inner-product definition | [Source](../lean/examples/finite_inner_product_definition/statement.lit) · [Lean](../lean/examples/finite_inner_product_definition/statement.lean) |
| Real coordinates after construction | [Source](../lean/examples/matrix_product_real_values/statement.lit) · [Lean](../lean/examples/matrix_product_real_values/statement.lean) |

The final checkpoint passed 18 new/affected pairs with strict source execution
and byte-identical independent generation. Fifteen received fresh Lean checks;
three reused identical output already checked against the same Core and
toolchain. All 27 exported theorems were audited with only `Classical.choice`,
`Quot.sound` and `propext`. The compiler module passed 1,253 tests, including
missing/reordered WD, changed summands/index ranges and removed left conjugation
(`phase6o-final`, `phase6o-compiler-regression`).

### Matrix constructor progress

Eighteen of the planned 23 constructor families now have checked compilation:
`matrix`, `zero_matrix`, `identity_matrix`, `transpose`, `conjugate_transpose`,
`trace`, `matrix_add`, `matrix_sub`, `matrix_scale`, `matrix_mul`, `matrix_apply`,
`diagonal_matrix`, `outer_product`, `inner_product`, `euclidean_norm` and
`frobenius_norm`, `det` and `matrix_power`. Their supported proof
routes are the examples and checkpoints above; this count does not cover every
matrix builtin theorem or exact-evaluation certificate.

Five constructor families remain: inverse, rank,
minor, cofactor and adjugate. Matrix-native Mathlib adapters remain separate work.


### Native template standard-return widening boundary

The native `TemplateApplicationInStandardSuperset` route now retains actual
numeric template return declarations, aliases and stored signatures after
application WD. See `examples/wd/template_standard_return.lit`. It enables a
bundled uniform probability source model, with the actual dice conditional2/3.
Intrinsic function-template Lean replay remains unsupported: the before CLI
already stops at `Template/Body`, and the new return consumer refuses
`FunctionReturn/TemplateStandardSuperset` explicitly. This increment adds no
Lean pair, axiom or mathematical semantics model. Existing named/anonymous
function-return compilation and forged-evidence controls are preserved.

### One-bound finite intersections,2026-10-27

The generated [source](../lean/examples/finite_intersection_one_bound/statement.lit)
and [Lean](../lean/examples/finite_intersection_one_bound/statement.lean) pair
replay finiteness from either operand and cardinality WD for an arbitrary set
intersected with a singleton. Each new strategy retains and validates its one
actual operand premise; the existing both-finite consumer is unchanged.
Missing/changed-side evidence is refused. All3 generated theorems pass Lean4.31.0
with pinned Mathlib and only the standard allowed axioms; this certifies the
finite-intersection slice, not the std Dirac probability structures.


## Phase 6p: finite vector and matrix norms, 2026-10-26

`euclidean_norm(v,n)` and `frobenius_norm(A,m,n)` now retain their natural
dimensions and complex vector/matrix membership proofs. Their representations
are the square roots of finite sums of squared complex magnitudes; zero
dimensions remain legal. Core proves real closure, nonnegativity and the
squared-norm identities. The compiler consumes the original WD and scalar
result branches, including explicit `euclidean_norm_square` and
`frobenius_norm_square` invocations and later named-theorem calls.

| Example | Checked source and generated Lean |
| --- | --- |
| Euclidean norm, R/C membership and zero dimension | [Source](../lean/examples/euclidean_norm/statement.lit) · [Lean](../lean/examples/euclidean_norm/statement.lean) |
| Frobenius norm and zero rows | [Source](../lean/examples/frobenius_norm/statement.lit) · [Lean](../lean/examples/frobenius_norm/statement.lean) |
| Vector nonnegativity and theorem reuse | [Source](../lean/examples/euclidean_norm_nonnegative/statement.lit) · [Lean](../lean/examples/euclidean_norm_nonnegative/statement.lean) |
| Matrix nonnegativity and theorem reuse | [Source](../lean/examples/frobenius_norm_nonnegative/statement.lit) · [Lean](../lean/examples/frobenius_norm_nonnegative/statement.lean) |
| Vector norm definition | [Source](../lean/examples/euclidean_norm_definition/statement.lit) · [Lean](../lean/examples/euclidean_norm_definition/statement.lean) |
| Matrix norm definition | [Source](../lean/examples/frobenius_norm_definition/statement.lit) · [Lean](../lean/examples/frobenius_norm_definition/statement.lean) |

The two definition examples explicitly assume the nonnegative finite sum needed
for the source `sqrt` WD. They check conditional unfolding; the separate
nonnegativity examples prove the norm's sign without that premise. Arbitrary
norm-value calculations and triangle/Cauchy–Schwarz rules are not part of this
batch. No Runtime, AST, result fields or model axioms changed.

Nine new/affected pairs passed strict source execution and byte-identical
independent generation. A subsequent cache audit found that the compiled-Core
metadata did not match the current Core hash. The current Core and all nine
unchanged generated files then received fresh Lean checks; all 18 exports
passed the standard axiom audit (`phase6p-current-core`). The local checker now
rejects a mismatched Core cache before checking or reusing generated files. The compiler
module passed 1,259 tests, including five focused norm tests for missing,
reordered or changed evidence and invalid dimensions/carriers. Local receipts:
`phase6p-final`, `phase6p-compiler-regression`.

The definition proofs bind their expanded object once. This reduced the vector
and matrix definition files from 296,303 to 247,433 bytes and from 937,704 to
781,747 bytes respectively. These files are still larger than the 6–8 KB
membership examples; the measurements do not claim a general output-size bound.

## Phase 6q: determinant, 2026-10-27

`det(A,n)` now retains the original natural-order and complex square-matrix WD.
Its representation uses Mathlib `Matrix.det` after observing the matrix's
complex entries; real input gives real output. The compiler replays the existing
`matrix_det_identity`, `matrix_det_transpose` and `matrix_det_adjoint` theorem
results, including their ordered requirements and subsequent named-theorem use.
Zero-order determinant is one, as in the source semantics and Mathlib.

| Example | Checked source and generated Lean |
| --- | --- |
| Complex and real determinant membership | [Source](../lean/examples/matrix_determinant/statement.lit) · [Lean](../lean/examples/matrix_determinant/statement.lean) |
| Identity determinant and theorem reuse | [Source](../lean/examples/matrix_determinant_identity/statement.lit) · [Lean](../lean/examples/matrix_determinant_identity/statement.lean) |
| Transpose determinant | [Source](../lean/examples/matrix_determinant_transpose/statement.lit) · [Lean](../lean/examples/matrix_determinant_transpose/statement.lean) |
| Conjugate-transpose determinant | [Source](../lean/examples/matrix_determinant_adjoint/statement.lit) · [Lean](../lean/examples/matrix_determinant_adjoint/statement.lean) |
| Zero-, one- and two-order definitions | [Source](../lean/examples/matrix_determinant_small_orders/statement.lit) · [Lean](../lean/examples/matrix_determinant_small_orders/statement.lean) |

The definition consumer validates the recorded expansion and compiles its
original residual proof. It currently accepts literal orders 0, 1 and 2;
higher-order expansions and further determinant laws remain unsupported.
Trace and determinant share their square-matrix WD consumer. No Runtime, AST,
result fields or model axioms changed.

Eight new/affected pairs passed strict source execution, independent identical
generation and real Lean checks. The final checkpoint freshly checked the
repaired small-order output and reused seven unchanged outputs already checked
against the same Core and toolchain. All 13 exports passed the standard axiom
audit. The compiler module passed 1,265 tests; four focused determinant tests
include missing/reordered WD, changed theorem conclusions, changed expansions
and invalid matrix domains. Local receipts: `phase6q-final`,
`phase6q-compiler-regression`. The five new generated files are 10–47 KB each.

## Phase 6r: natural matrix powers, 2026-10-27

`matrix_power(A,n,p)` keeps its original three operands and WD proofs:
`n,p ∈ N` and `A ∈ matrix(C,n,n)`. Core defines the value by natural recursion
from the identity matrix, using the existing matrix multiplication at each
successor. Its denotation is independent of the supplied WD proofs. Real
matrices retain real output; zero dimensions and exponent zero remain legal.

The compiler validates the original callable formula for literal zero,
positive literals and symbolic exponents. For symbolic powers this includes
the recorded fold's range, constant input function, multiplication order and
identity seed. It replays `matrix_power_zero` and `matrix_power_successor`
applications with their original requirements, stores and conclusion WD.

| Example | Checked source and generated Lean |
| --- | --- |
| Natural powers over C and R | [Source](../lean/examples/matrix_power_membership/statement.lit) · [Lean](../lean/examples/matrix_power_membership/statement.lean) |
| Zero and positive literal exponents | [Source](../lean/examples/matrix_power_literal/statement.lit) · [Lean](../lean/examples/matrix_power_literal/statement.lean) |
| Zero-dimensional matrices | [Source](../lean/examples/matrix_power_empty/statement.lit) · [Lean](../lean/examples/matrix_power_empty/statement.lean) |
| Zeroth power and named-theorem reuse | [Source](../lean/examples/matrix_power_zero/statement.lit) · [Lean](../lean/examples/matrix_power_zero/statement.lean) |
| Successor power | [Source](../lean/examples/matrix_power_successor/statement.lit) · [Lean](../lean/examples/matrix_power_successor/statement.lean) |
| Matrix and power aliases | [Source](../lean/examples/matrix_power_alias/statement.lit) · [Lean](../lean/examples/matrix_power_alias/statement.lean) |

All six pairs passed strict source execution, independent identical generation
and fresh Lean checks; their 11 exported theorems passed the standard axiom
audit. Generated files are approximately 7–34 KB. No Runtime, AST, result field
or model axiom changed. The power-addition theorem, coordinate evaluation,
whole fold-definition equality and native Mathlib adapters remain separate
coverage; validating a callable certificate does not compile all those routes.

The batch checkpoint also checked three affected matrix pairs: nine pairs in
total, with three fresh checks and six unchanged same-Core reuses at the final
gate, and 16 audited exports. Compiler regression passed 1,270 tests; one stale
set-difference route assertion was updated and passed a focused rerun. That
existing source/generated pair was regenerated and independently checked in
Lean as well. Receipts: `phase6r-final`, `phase6r-compiler-regression`,
`phase6r-set-difference` and `phase6r-set-difference-test`.


## Phase 6s: deleted-row/column matrices, 2026-10-27

`matrix_minor(A,n,r,c)` retains all four source operands and the five ordered
WD results: `n ∈ N+`, `r,c ∈ closed_range(1,n)`, `n ∈ N`, and
`A ∈ matrix(C,n,n)`. Core interprets it as the original matrix evaluated at
`k + floor((k+n-deleted)/n)` in each coordinate. Proved index bounds establish
that these coordinates stay in range and omit the deleted row/column. The
object's denotation remains independent of its WD proofs; no Runtime, AST,
result shape or model axiom changed.

| Example | Checked source and generated Lean |
| --- | --- |
| Complex and real matrix membership | [Source](../lean/examples/matrix_minor_membership/statement.lit) · [Lean](../lean/examples/matrix_minor_membership/statement.lean) |
| Coordinates on either side of a deleted index | [Source](../lean/examples/matrix_minor_coordinates/statement.lit) · [Lean](../lean/examples/matrix_minor_coordinates/statement.lean) |
| Deleting the only row and column | [Source](../lean/examples/matrix_minor_empty/statement.lit) · [Lean](../lean/examples/matrix_minor_empty/statement.lean) |
| A coordinate theorem and its application | [Source](../lean/examples/matrix_minor_theorem/statement.lit) · [Lean](../lean/examples/matrix_minor_theorem/statement.lean) |
| Matrix and minor aliases | [Source](../lean/examples/matrix_minor_alias/statement.lit) · [Lean](../lean/examples/matrix_minor_alias/statement.lean) |

All five pairs passed strict source execution, independent identical generation,
fresh Lean 4.31.0 checks and a 12-export axiom audit. Generated files range from
9,518 to 199,285 bytes. The compiler regression passed all 1,275 tests. Negative
checks reject missing/reordered WD, swapped row/column evidence, changed
callable formulas, zero order, out-of-range indices and nonsquare input.
The final affected-pair gate covered eight pairs and 18 exports: five unchanged
same-Core reuses and three fresh checks, including the approved nonempty-family
intersection example. Receipts: `phase6s-first`, `phase6s-final`, and
`phase6s-compiler-regression` in the local compiler workspace.

Standalone membership examples preserve the producer's `n-1` dimension form:
for `n=1` this is `matrix(C,1-1,1-1)`. Simplified dimensions `0`/`1` needed
additional context in the source verifier, and real closure through two aliases
needed prior operand membership. These are recorded source boundaries. The
general equality to a complete anonymous-function formula is also not delivered:
its source WD cannot yet prove the floor-based shifted-index bound. Coordinate
expansion is covered separately and consumes the successful recorded result.

Matrix constructor entrypoints now stand at 19 of 23. Cofactor, adjugate,
inverse and rank remain; this count does not imply coverage of every rule or a
native Mathlib adapter for each constructor.


## Phase 6t: cofactors and cited matrix returns, 2026-10-27

`matrix_cofactor(A,n,r,c)` now has its own Lean representation. It retains the
same four operands and five ordered WD requirements as `matrix_minor`:
positive order, two valid deleted indices, natural order and square complex
input. The two constructors share the compiler's WD consumer. Core defines the
cofactor as the signed determinant of the deleted-row/column matrix, with the
sign and dimension observed from the original numeric objects. WD proofs do
not select the value. Complex and real membership are proved in Core.

The compiler consumes both the native carrier result and the intrinsic
complex-member certificate. For scalar definitions it validates and replays
the producer's literal `1×1` and `2×2` expansions, including both negative
entries; it retains the original residual proof. Aliases and a named theorem
applied to a zero matrix are covered.

That theorem application exposed another consumer gap: a call can have native
matrix WD while its result cites a stored function signature. The compiler now
checks their complete domains and consumes the cited membership for codomain
or standard-set inclusion. Missing citations and altered domains are rejected.
No Runtime, AST, result shape, model axiom or compiler state was added.

| Example | Checked source and generated Lean |
| --- | --- |
| Cofactors over C and R | [Source](../lean/examples/matrix_cofactor_membership/statement.lit) · [Lean](../lean/examples/matrix_cofactor_membership/statement.lean) |
| One-by-one and all four two-by-two cofactors | [Source](../lean/examples/matrix_cofactor_small_orders/statement.lit) · [Lean](../lean/examples/matrix_cofactor_small_orders/statement.lean) |
| Named matrix and cofactor | [Source](../lean/examples/matrix_cofactor_alias/statement.lit) · [Lean](../lean/examples/matrix_cofactor_alias/statement.lean) |
| Negative cofactor theorem and concrete application | [Source](../lean/examples/matrix_cofactor_theorem/statement.lit) · [Lean](../lean/examples/matrix_cofactor_theorem/statement.lean) |
| Stored real/complex function carriers with native matrix WD | [Source](../lean/examples/matrix_cited_function_returns/statement.lit) · [Lean](../lean/examples/matrix_cited_function_returns/statement.lean) |

All five pairs passed strict source execution, identical independent generation,
fresh Lean 4.31.0 checks and a 13-export standard axiom audit. Files range from
13,047 to 84,108 bytes. All 1,281 compiler tests passed. The final nine-pair gate
included four fresh matrix/carrier checks and five unchanged same-Core reuses,
with 21 audited exports. Local receipts: `phase6t-first`, `phase6t-final`,
`phase6t-compiler-regression`, `phase6t-return-tests` and `phase6t-boundary`.

The executable boundary uses a valid Litex `3×3` cofactor expansion: source
verification succeeds, and compilation rejects `Matrix/CofactorExpansionOrder`
without emitting a partial Lean artifact. Higher-order scalar expansions,
general definition equality and native Mathlib adapters remain separate work.
Matrix constructor entrypoints are now 20 of 23: adjugate, inverse and rank
remain.


## Phase 6u: adjugates, 2026-10-27

`matrix_adjugate(A,n)` consumes the original two child WD results and two
requirements: `n $in N` and `A $in matrix(C,n,n)`. Its Lean object denotes the
function whose `(r,c)` entry is `matrix_cofactor(A,n,c,r)`. Core proves complex
and real matrix membership. Zero order remains legal: positive order is derived
only inside a coordinate proof, from a valid index in `closed_range(1,n)`.

The compiler validates the original callable formula, including the exchanged
indices and the complete scalar signature. It replays coordinate expansion,
whole-function definition equality, aliases and named theorem applications.
The cofactor's existing denotation is factored into a pure value function so
bound formula parameters can use it; the old and new definitions are
definitionally equal. No Runtime, AST, result shape or compiler state changed.

| Example | Checked source and generated Lean |
| --- | --- |
| Complex and real square matrices | [Source](../lean/examples/matrix_adjugate_membership/statement.lit) · [Lean](../lean/examples/matrix_adjugate_membership/statement.lean) |
| Real values at valid coordinates | [Source](../lean/examples/matrix_adjugate_real_values/statement.lit) · [Lean](../lean/examples/matrix_adjugate_real_values/statement.lean) |
| Transposed cofactor coordinates | [Source](../lean/examples/matrix_adjugate_coordinates/statement.lit) · [Lean](../lean/examples/matrix_adjugate_coordinates/statement.lean) |
| Zero-order adjugate | [Source](../lean/examples/matrix_adjugate_empty/statement.lit) · [Lean](../lean/examples/matrix_adjugate_empty/statement.lean) |
| Complete formula function | [Source](../lean/examples/matrix_adjugate_definition/statement.lit) · [Lean](../lean/examples/matrix_adjugate_definition/statement.lean) |
| Matrix and adjugate aliases | [Source](../lean/examples/matrix_adjugate_alias/statement.lit) · [Lean](../lean/examples/matrix_adjugate_alias/statement.lean) |
| Named coordinate theorem and concrete application | [Source](../lean/examples/matrix_adjugate_theorem/statement.lit) · [Lean](../lean/examples/matrix_adjugate_theorem/statement.lean) |
| Off-diagonal entry via a cofactor and cited equalities | [Source](../lean/examples/matrix_adjugate_two_steps/statement.lit) · [Lean](../lean/examples/matrix_adjugate_two_steps/statement.lean) |

All eight pairs passed strict source execution, identical independent generation,
fresh Lean 4.31.0 checks and a 14-export standard axiom audit. Generated files
range from 3,501 to 77,553 bytes. Four focused Rust tests cover the successful
routes and rejection of missing/reordered WD, an untransposed cofactor formula,
missing or wrong real-carrier evidence, altered domains, negative dimensions,
nonsquare inputs and invalid coordinates.

The two-step example retains the intermediate cofactor equality because the
single direct source goal `matrix_adjugate(A,2)(1,2) = -A(1,2)` did not verify.
The valid explicit call `release thm matrix_adjugate_identity(zero_matrix(2,2),2)`
is an executable unsupported boundary: compilation rejects its theorem contract
and emits no partial Lean file. The adjugate multiplication identity and native
Mathlib adapters are not delivered by this constructor batch.

Matrix constructor entrypoints now stand at 21 of 23; inverse and rank remain.

Batch verification: all 1,287 compiler tests passed. The affected-pair gate
checked twelve pairs and 26 exports: seven unchanged same-Core reuses and five
fresh checks (four cofactor pairs plus nonempty-family intersection). The eighth
new pair, real coordinate membership, passed a separate fresh check and
one-export axiom audit. Local receipts: `phase6u-first`, `phase6u-values`,
`phase6u-final`, `phase6u-compiler-regression` and `phase6u-boundary`.


## Phase 6v: guarded inverse matrices, 2026-10-27

`matrix_inverse(A,n)` retains children `[A,n]` and the original ordered WD:
`n $in N`, `A $in matrix(C,n,n)`, then `det(A,n) != 0`. Its graph has entry
`matrix_cofactor(A,n,c,r) / det(A,n)`. Core derives complex and real matrix
membership and coordinate values from the existing graph, cofactor, determinant
and division laws. Zero order is allowed when its determinant is nonzero.

For example, the following source compiles with the determinant condition
carried into the inverse object:

```litex
forall n N+, A matrix(C,n,n), r closed_range(1,n), c closed_range(1,n):
    det(A,n) != 0
    =>:
        matrix_inverse(A,n)(r,c) = matrix_cofactor(A,n,c,r) / det(A,n)
```

The compiler checks the transposed cofactor indices, denominator, complete
function signature and original real-carrier evidence. It supports whole-function
definition equality, aliases, named coordinate theorems and explicit two-step
computations. No Runtime, AST, result shape or compiler state changed in this batch.

| Example | Checked source and generated Lean |
| --- | --- |
| Complex and real inverse matrices | [Source](../lean/examples/matrix_inverse_membership/statement.lit) · [Lean](../lean/examples/matrix_inverse_membership/statement.lean) |
| Coordinate quotient | [Source](../lean/examples/matrix_inverse_coordinates/statement.lit) · [Lean](../lean/examples/matrix_inverse_coordinates/statement.lean) |
| Complete defining function | [Source](../lean/examples/matrix_inverse_definition/statement.lit) · [Lean](../lean/examples/matrix_inverse_definition/statement.lean) |
| Real coordinate values | [Source](../lean/examples/matrix_inverse_real_values/statement.lit) · [Lean](../lean/examples/matrix_inverse_real_values/statement.lean) |
| Zero-order inverse | [Source](../lean/examples/matrix_inverse_empty/statement.lit) · [Lean](../lean/examples/matrix_inverse_empty/statement.lean) |
| Off-diagonal entry through a cofactor | [Source](../lean/examples/matrix_inverse_two_steps/statement.lit) · [Lean](../lean/examples/matrix_inverse_two_steps/statement.lean) |
| Guarded theorem and concrete application | [Source](../lean/examples/matrix_inverse_theorem/statement.lit) · [Lean](../lean/examples/matrix_inverse_theorem/statement.lean) |
| Matrix and inverse aliases | [Source](../lean/examples/matrix_inverse_alias/statement.lit) · [Lean](../lean/examples/matrix_inverse_alias/statement.lean) |

Two original result branches were needed by these examples:

- `ClosedRangeLiteralExpansion` now validates literal integer endpoints and the
  exact ordered enumeration, including an empty interval. Its finite-list bound
  remains the native rule's 1,024 entries. Lean checks the corresponding membership
  equivalence by set extensionality. See [integer intervals](../lean/examples/closed_integer_range_enumeration/).
  The native rule does not accept a parsed negative-expression endpoint such as
  `closed_range(-1,1)`; this batch does not widen source search.
- A small determinant's `ExactEvaluation` result now consumes the original ordered
  function evaluations for identity/zero-matrix entries, their call WD and beta
  expansions, then rational arithmetic. Missing, reordered or changed evaluations
  are rejected. Other source kinds, nested scalar/aggregate evidence and extra
  equality citations remain unsupported by this leaf. See [exact determinants](../lean/examples/matrix_determinant_exact/).

All ten new source/generated pairs passed strict source execution, independent
identical generation and actual Lean 4.31.0 checks; their 26 exports passed the
standard axiom audit. Generated files range from 9,999 to 125,713 bytes. The final
inverse/affected-pair gate checked ten pairs and 25 exports: four unchanged
same-Core reuses and six fresh checks. The two consumer pairs were checked fresh
in a separate six-export gate. All 1,294 compiler tests passed, including two
focused interval tests and the 61-test matrix module. Local receipts are
`phase6v-consumers`, `phase6v-inverse`, `phase6v-matrix-tests` and
`phase6v-compiler-regression`.

The valid source call `release thm matrix_inverse_laws(identity_matrix(2),2)`
remains an executable unsupported boundary: after proving the nonzero determinant,
compilation reaches that third statement, rejects `BuiltinMembership/Contract`,
and emits no partial artifact. General inverse multiplication laws, higher-order
scalar expansions and native Mathlib adapters are separate work. Matrix
constructor entrypoints now stand at 22 of 23; `matrix_rank` remains.


## Phase 6w: matrix rank, 2026-10-27

`matrix_rank(A,m,n)` now wraps Mathlib's `Matrix.rank` on the existing finite
complex-matrix observation. It preserves children `[A,m,n]` and WD
`[m∈N,n∈N,A∈matrix(C,m,n)]`. Zero dimensions remain legal. The result is a
Litex object with natural-number denotation; membership in larger standard
number sets follows the original recorded inclusion evidence.

Replay includes both direct matrix scalar membership and the separate intrinsic
natural-codomain result used by comparisons and carrier widening. Three existing
explicit theorem IDs are supported: `matrix_rank_bounds/3`, `matrix_rank_zero/2`
and `matrix_rank_identity/1`. Their original requirements, stores and ordered
conclusions are checked. Core proves row/column bounds, zero-matrix rank and
identity-matrix rank from Mathlib. No Runtime, AST, result shape, model field or
compiler state was added.

```litex
thm checked_matrix_rank_bounds:
    ? forall m,n N, A matrix(C,m,n):
        matrix_rank(A,m,n) <= m
        matrix_rank(A,m,n) <= n
    release thm matrix_rank_bounds(A,m,n)
```

Rank aliases consume the original three congruence children—matrix, rows,
columns—rather than recomputing equality. The generated application explicitly
fixes the `M.Value` domains of `congr`. Formula functions can return rank using
the same pure denotation and captured natural-codomain proof.

| Example | Checked source and generated Lean |
| --- | --- |
| Natural membership and standard number inclusion | [Source](../lean/examples/matrix_rank_membership/statement.lit) · [Lean](../lean/examples/matrix_rank_membership/statement.lean) |
| Both dimension bounds and named theorem reuse | [Source](../lean/examples/matrix_rank_bounds/statement.lit) · [Lean](../lean/examples/matrix_rank_bounds/statement.lean) |
| Rectangular zero matrices | [Source](../lean/examples/matrix_rank_zero/statement.lit) · [Lean](../lean/examples/matrix_rank_zero/statement.lean) |
| Identity matrices | [Source](../lean/examples/matrix_rank_identity/statement.lit) · [Lean](../lean/examples/matrix_rank_identity/statement.lean) |
| Empty row/column index sets | [Source](../lean/examples/matrix_rank_empty/statement.lit) · [Lean](../lean/examples/matrix_rank_empty/statement.lean) |
| Matrix and rank aliases | [Source](../lean/examples/matrix_rank_alias/statement.lit) · [Lean](../lean/examples/matrix_rank_alias/statement.lean) |
| A natural-valued function on matrices | [Source](../lean/examples/matrix_rank_function/statement.lit) · [Lean](../lean/examples/matrix_rank_function/statement.lean) |

All seven pairs passed strict source execution, independent identical generation
and actual Lean 4.31.0 checks. Their 23 generated theorem declarations occupy
10,090–30,553 bytes per file. The first six successful files were retained while
the alias elaboration failure was repaired and checked separately.
The final related gate checked eleven pairs and audited 35 exported theorems:
seven unchanged rank files reused their successful same-Core Lean checks; four
related files were checked fresh. Only `Classical.choice`, `Quot.sound` and
`propext` occurred in the axiom audit. All 1,299 compiler tests passed after the
final alias repair. Local receipts are `phase6w-final` and
`phase6w-compiler-final`.

The valid source `release thm matrix_rank_transpose(identity_matrix(2),2,2)`
remains unsupported: compilation rejects `BuiltinMembership/Contract` with zero
stdout bytes. Further rank laws, factorizations and exact elimination certificates
are separate proof routes. The original matrix-constructor inventory is now
**23/23**; this count does not count all matrix theorems or proof strategies.


## Phase 7a: real-set bounds and boundedness, 2026-10-27

Four more atomic result variants are connected: `RealSetBoundFact`,
`NotRealSetBoundFact`, `RealSetBoundedFact` and `NotRealSetBoundedFact`.
They represent five source predicates and their negations:

| Source predicate | Original WD | Meaning |
| --- | --- | --- |
| `$is_real_upper_bound(A,b)` | `A ⊆ R`, `b ∈ R` | Every member of `A` is at most `b` |
| `$is_real_lower_bound(A,b)` | `A ⊆ R`, `b ∈ R` | Every member of `A` is at least `b` |
| `$is_real_bounded_above(A)` | `A ⊆ R` | A real upper bound exists |
| `$is_real_bounded_below(A)` | `A ⊆ R` | A real lower bound exists |
| `$is_real_bounded(A)` | `A ⊆ R` | A lower bound and an upper bound exist |

Negative predicates retain the same domains. No nonempty premise is added:
the empty real set is bounded. Source verification, Runtime, AST and result
shapes are unchanged.

The compiler consumes the original definition children, in their recorded order:
one universal inequality for a bound; lower then upper existence for two-sided
boundedness. Definition inference retains each stored FactId, including the two
one-sided projections. Assumptions, conclusions, negative fact citations,
existential witness extraction, named theorem calls and equality transport all
have generated examples. Missing/reordered domain or definition evidence and
changed inference identities are rejected.

Core boundedness uses the compiler's existing proof-dependent existential shape,
`∃ b, ∃ h : In b R, ...`. The new `by def` examples also exposed a missing branch
in semantic-dependency discovery: the existing scan now checks the verified
`by def` subject and its inference results, so a literal set in that statement
requests `SetSemantics`. No compiler state or replacement proof search was added.

`realMemberSet M (denote A)` observes the source set as an ordinary `Set ℝ`.
Four proved Core equivalences connect bounds and boundedness to Mathlib's
`upperBounds`, `lowerBounds`, `BddAbove` and `BddBelow`, using the original
real-set and real-bound premises. This is a proved semantic bridge; the batch
does not automatically generate a native adapter or choose a concrete model.

| Example | Checked source and generated Lean |
| --- | --- |
| All ten positive/negative predicate forms | [Source](../lean/examples/real_set_bound_citations/statement.lit) · [Lean](../lean/examples/real_set_bound_citations/statement.lean) |
| Equal sets and equal bounds | [Source](../lean/examples/real_set_bound_citations/substitution.lit) · [Lean](../lean/examples/real_set_bound_citations/substitution.lean) |
| A reusable upper-bound theorem and concrete call | [Source](../lean/examples/real_set_bound_theorem/statement.lit) · [Lean](../lean/examples/real_set_bound_theorem/statement.lean) |
| Empty-set boundedness | [Source](../lean/examples/real_empty_set_bounds/statement.lit) · [Lean](../lean/examples/real_empty_set_bounds/statement.lean) |
| Singleton bounds and witnesses | [Source](../lean/examples/real_singleton_bounds/statement.lit) · [Lean](../lean/examples/real_singleton_bounds/statement.lean) |
| One-sided components and witness extraction | [Source](../lean/examples/real_set_bounded_components/statement.lit) · [Lean](../lean/examples/real_set_bounded_components/statement.lean) |

All six new pairs passed strict source verification, independent identical
generation and actual Lean 4.31.0 checks: 50 new exports, 4,045–19,533 bytes
per file. The final related gate covers eight pairs and 56 exports, with seven
unchanged same-Core Lean checks reused and the repaired theorem example checked
fresh. All 1,306 compiler tests passed, including seven focused bounds tests.
The generated exports and six new Core bridge laws use only `Classical.choice`,
`Quot.sound` and `propext`. Local receipts: `phase7a-accepted`,
`phase7a-compiler-accepted`, `phase7a-tests-set-dependency` and
`RealBoundsBridgeAudit`.

Supremum/infimum objects and their explicit theorem releases are next.
`release thm real_supremum_exists({2})`, after its checked boundedness
prerequisites, remains an executable boundary: source succeeds, compilation
rejects statement 4 at `BuiltinMembership/Contract`, with no partial output.
The native verifier also does not prove `by def $is_real_upper_bound({1,2},2)`
without additional proof steps; this batch does not alter that search behavior.


## Phase 7b: real supremum and infimum, 2026-10-27

Two more constructors are connected: `sup(A)` and `inf(A)`. They consume the
existing ordered set WD, real-subset proof and either a concrete extremal
certificate or its existential proof. Runtime, AST and result shapes are
unchanged. A constructor's denotation is independent of its WD proof.

Core interprets the reserved predicates `is_real_least_upper_bound/2` and
`is_real_greatest_lower_bound/2` using a nonempty real source set and Mathlib
`IsLUB`/`IsGLB` on `realMemberSet`. Selection denotes the corresponding `sSup`
or `sInf`. These predicates remain ordinary facts over generic source objects;
no membership proof changes a parameter's host representation. This connects
two reserved predicate names, not two additional `AtomicFact` variants.

The four explicit theorem consumers are `real_supremum_exists/1`,
`real_infimum_exists/1`, `real_supremum_selected/1` and
`real_infimum_selected/1`. Each checks its original ID, arguments, ordered
premises, stores and conclusion WD. Candidate-value equalities replay
`RealBounds` and its exact known certificate and value-equality child.
Congruence replays the recorded equality of the two source sets.

Function bodies use the same pure denotation during recorded beta expansion.
The function examples also exercise a newly connected existing inference:
`A $in power_set(R)` stores `A $subset R` at its original FactId. The compiler
now emits that projection with `inPowerSet_iff`, making it available to later
WD instead of reconstructing it. This projection currently requires the
recorded carrier to be a direct `power_set` constructor; other carrier
resolution routes need their own evidence consumer.

| Mathematical problem | Source | Generated Lean |
| --- | --- | --- |
| Select the supremum of `{2}` from boundedness | [Source](../lean/examples/real_supremum_selection/statement.lit) | [Lean](../lean/examples/real_supremum_selection/statement.lean) |
| Select the infimum of `{2}` from boundedness | [Source](../lean/examples/real_infimum_selection/statement.lit) | [Lean](../lean/examples/real_infimum_selection/statement.lean) |
| A known supremum candidate determines the value; reuse and aliases | [Source](../lean/examples/real_supremum_candidate/statement.lit) | [Lean](../lean/examples/real_supremum_candidate/statement.lean) |
| The corresponding infimum laws | [Source](../lean/examples/real_infimum_candidate/statement.lit) | [Lean](../lean/examples/real_infimum_candidate/statement.lean) |
| Select extrema inside guarded functions on real subsets | [Source](../lean/examples/real_extremum_functions/statement.lit) | [Lean](../lean/examples/real_extremum_functions/statement.lean) |

At the phase 7b checkpoint, certificate introduction and projection were not
connected. The following boundary is now covered by phase 7c below:

```litex
by def $is_real_upper_bound({2},2)
release thm real_least_upper_bound_from_definition({2},2)
sup({2}) = 2
```

Before phase 7c, this source verified but compilation rejected the second
statement at `BuiltinMembership/Contract` with no partial file. Empty, unbounded and
nonreal sets without valid selection evidence still fail source WD.

Acceptance: five new strict source/generated pairs, 28 new theorem exports,
8,403–27,651 bytes per file. The final related gate checks seven pairs and
49 exports with independent identical regeneration and fresh Lean 4.31.0
checks. All 1,311 compiler tests pass, including five focused tests covering
changed theorem stages, swapped WD, malformed power-set projections and invalid
source selection. Generated exports and the six Core extrema laws use only
`Classical.choice`, `Quot.sound` and `propext`. Local receipts are
`phase7b-final`, `phase7b-all-compiler`, `phase7b-focused-accepted`,
`RealExtremaAudit` and `phase7b-boundary`.


## Phase 7c: extremal-certificate theorem calls, 2026-10-27

Fourteen existing theorem IDs now compile: seven upper/lower pairs for definition,
bound projection, existence from an explicit bound, uniqueness, comparison with
a member, comparison with another bound, and strict crossing witnesses.
Together with phase 7b, all eighteen supremum/infimum theorem IDs in these two
native contract families have consumers. This does not cover all real-analysis
builtin theorems.

```litex
by def $is_real_upper_bound({2},2)
release thm real_least_upper_bound_from_definition({2},2)
sup({2}) = 2
```

This formerly rejected source now generates checked Lean. The complete
[supremum example](../lean/examples/real_supremum_certificate_laws/statement.lit)
and its [generated Lean](../lean/examples/real_supremum_certificate_laws/statement.lean)
also identify a second candidate, compare it with a bound, extract a crossing
member, and reuse a theorem over an arbitrary real set. The
[infimum source](../lean/examples/real_infimum_certificate_laws/statement.lit) and
[Lean](../lean/examples/real_infimum_certificate_laws/statement.lean) exercise
the corresponding lower-bound contracts.

The consumer validates each original theorem ID, argument list, ordered premise,
quantifier carrier, comparison direction, stored FactId and conclusion WD.
For nested extremality, the Core law's semantic bound is projected into the
original source `forall` premise. Only the required fresh schema binder is
specialized to the model universe; source object carriers remain generic.
No Runtime, AST, result-shape or search changes were needed.

Both new pairs pass strict Litex verification, independent identical generation
and actual Lean 4.31.0 checks: 46 exported theorems, 76,045 and 71,039 bytes.
The related gate checks seven pairs and 74 exports afresh. All 1,314 compiler
tests pass, including the eight focused extrema tests. The generated exports
and fourteen new Core laws use only `Classical.choice`, `Quot.sound` and
`propext`. Receipts: `phase7c-accepted`, `RealExtremumCertificateAudit` and
`phase7c-all-compiler` in the existing local compiler workspace.

### Common remaining work

| Order | Existing source capabilities still needing compiler work |
| --- | --- |
| Next analysis | `lim`, `limsup`, `liminf` and their recorded certificates. Phase 7d below covers monotonicity, boundedness, Cauchy, convergence and a specified real limit. |
| Following | `fn_lim`, function continuity and Lipschitz facts; derivative and Riemann-integral facts and selectors |
| Later analysis | Multivariable limits, partial/total derivatives, gradient/Jacobian/Hessian and related operators |
| Statement follow-up | Local templates, local piecewise/recursive functions and local functions selected from unique existence |
| Separate contracts | `algo by cases`, `algo by induc`, `strategy`; `eval` beyond the exact scalar slice below |

At the phase 7c checkpoint, the original analysis inventory had 17 unconnected
object constructors and 28 atomic variants without proposition rendering. Several mathematical properties
share a variant, so these numbers do not count individual predicates. Existing
object consumers can also lack specific equality/strategy/BT result branches.
For example, `release thm real_archimedean_natural_upper_bound(3)` verifies in
Litex but still rejects at `BuiltinMembership/Contract` with zero generated bytes;
`phase7c-boundary.json` records this executable boundary.


## Phase 7d: sequence monotonicity and boundedness, 2026-10-27

Seven existing sequence properties now replay into Lean: nondecreasing,
nonincreasing, strictly increasing, strictly decreasing, bounded above, bounded
below and bounded. Their positive/negative citations, equality substitution,
original definition clauses, named theorem reuse and inferred bound witnesses
are covered. Indexing remains `N+`; the complete function signature must return
`R` and have no additional guards.

```litex
have fn a(n N+) R = n
by def $is_seq_nondecreasing(a)
```

See [monotonicity](../lean/examples/sequence_monotonicity/),
[property citations](../lean/examples/sequence_property_citations/) and
[range bounds](../lean/examples/sequence_range_bounds/). Their three statement
pairs pass strict Litex, independent identical generation and actual Lean 4.31.0
checking: 33 exported theorems and 49,192–65,679 bytes per generated file.

The compiler reuses the signature already carried by `seq(R)` and its stored
function-set expansion. Inferred ranges of function parameters use the exact
original parameter membership. Negation's strict/weak order rules reuse their
recorded reversed premises. Runtime, AST, result shapes and search are unchanged.

The epsilon-tail follow-up below adds Cauchy/convergence definitions and a
specified sequence limit. `lim`/`limsup`/`liminf` selectors and native Mathlib
sequence adapters remain pending.
The wider range inclusion `fn_range(a) $subset C` for `a seq(R)` also remains
an unaccepted route: source verification succeeds, but compilation still
requests a missing standalone `N+` constructor. The local
`sequence_range_widening.lit` fixture preserves that boundary.

The additional [declared-codomain example](../lean/examples/sequence_range_bounds/containment.lit)
checks `fn_range(a) $subset R` directly. Its generated pair adds one export
and passes Lean. The related gate covers eight pairs and 47 exports, with
independent identical generation and standard axioms only; identical files
reuse prior Lean checks under the same Core/toolchain. Seven focused Rust tests
pass, including changed domains, reversed comparisons, altered inference IDs,
reordered bound witnesses and changed range certificates.

The normal Cargo test build is blocked by a missing tracked fixture:
`examples/_internal/regression/lambda_alpha_equivalence.lit`. These seven tests
were compiled from their canonical test module against the current library,
using the repository's configured 64 MiB test-thread stack. No full compiler
regression is claimed for this increment. Receipts: `phase7d-first-seven-accepted`,
`phase7d-isolated-tests` and `phase7d-journal` in the local compiler workspace.

### Phase 7d follow-up: Cauchy tails and specified limits, 2026-10-27

The compiler now consumes `$is_seq_cauchy(a)`, `$is_seq_convergent(a)` and
`$has_seq_limit(a,L)`, including their negations in citations and equality
transport. The sequence must have the complete unary `N+ → R` signature without
extra guards, and the specified limit must carry its original real-membership
evidence. The public Litex interfaces and Runtime/result shapes are unchanged.

For example, the [limit definition](../lean/examples/sequence_limit_definition/statement.lit)
uses this premise to prove `$has_seq_limit(a,L)` through `by def`:

```litex
forall epsilon R+:
    exist cutoff N+ st {{n N+: n >= cutoff} $subset preimage_set(a, {v R: abs(v-L) < epsilon})}
```

Core defines the tail, epsilon ball and limit predicate using the existing
set/function semantics. The compiler checks the original binders, carriers,
comparisons, preimage function and child proofs before emitting the bridge
application. Cauchy uses pairs of tail indices. Its stored definition supplies
the controlling-tail existence; convergence supplies a real limit witness.
See the [Cauchy example](../lean/examples/sequence_cauchy_definition/),
[convergence witness and theorem reuse](../lean/examples/sequence_convergence_witness/)
and [positive/negative limit citations](../lean/examples/sequence_limit_citations/).

Whole-forall reuse now matches nested set-builder binders and preimage sets.
Visible WD constructors may be reused after local binder renaming, with free
references, carriers and active scope boundaries retained. Recorded compound
alpha-equality also covers Cartesian products, tuples and preimage sets. These
changes consume original evidence; they do not introduce a search or WD store.

All four new source/generated pairs pass strict Litex, independent identical
generation and Lean 4.31.0: 12 exported theorems, 13,070–55,891 bytes per file.
The related gate checks 12 pairs and 59 exports under the updated Core, with
only `Classical.choice`, `Quot.sound` and `propext`. Fifteen canonical Rust tests
pass through the current-library harness, including malformed epsilon clauses,
wrong real-value evidence, missing inferences and changed forall citations.
The full Cargo compiler suite remains unrun because of the missing fixture
reported above. Receipts: `phase7d-epsilon-accepted`,
`phase7d-epsilon-isolated-tests` and `phase7d-epsilon-journal` in the existing
local compiler workspace.

The shared binder/WD changes also pass the existing set-valued-function and
compound-theorem-return pairs: two more pairs and seven exports, bringing this
increment's focused Lean checks to 14 pairs and 66 exports.

This does not yet compile `lim`, `limsup`, `liminf`, general limit BTs or a
native Mathlib sequence adapter. The following checkpoint adds exact scalar
`eval`; local definitions, `strategy` and `algo` remain separate follow-ups.

## Exact scalar `eval`, 2026-10-27

The compiler consumes `ExecStmtResult::Command(Eval(Success(...)))` directly.
For example:

```litex
have eval_input_a R = 10
eval eval_input_a + 1
eval_input_a + 1 = 11
```

The result supplies the original source WD, rewritten object, ordered cited
equality IDs, evaluated object, equality WD and store/inference result. The
compiler validates their subjects, translates the recorded substitutions,
checks the exact scalar computation with the existing numeric semantic laws,
and publishes the original equality and its inferences. It adds no Runtime,
AST, result fields or Core axioms.

Closed numeric evaluation omits per-node carrier searches in its original WD.
Within that original evaluation scope, the compiler derives those memberships
from exact numeric denotations. Division still consumes the recorded nonzero
proof. Numeric negative powers also prove their nonzero base condition.
The existing positive-power inference consumer now exposes a completed
positivity check's WD before extracting its real-membership facts.

| Pair | Checked content |
| --- | --- |
| [Arithmetic](../lean/examples/evaluated_arithmetic/) | Fractions, finite decimals, four operations, negation, positive and negative integer powers, stored-equality reuse |
| [Citations](../lean/examples/evaluated_numeric_citations/) | One and two previously proved object values, ordered substitutions and repeated operands |
| [Local scope](../lean/examples/evaluated_local_facts/) | Evaluation inside a sketch; the same source name can be reused outside |

All three sources pass strict Litex verification and independent byte-identical
Lean generation. Their 23 exported theorems pass Lean 4.31.0 and the axiom audit
with only `propext`, `Classical.choice` and `Quot.sound`. The arithmetic file is
108,239 bytes; the other two are 5,872 and 5,087 bytes. Final checks reused
already checked identical bytes for the latter two with unchanged Core and
toolchain. Eight related pairs also pass regeneration and Lean checks, covering
18 exports; four sequence pairs reuse checked identical bytes, while four
arithmetic/scope pairs receive fresh Lean checks.

Thirty canonical Rust tests pass through the current-library harness: nine
evaluation tests, six positive-power inference tests and fifteen sequence
regressions. Rejection controls cover altered endpoints and values, wrong or
reordered citations, self/future/closed-local references, missing WD/guards,
wrong constructor tags and changed stores. The full Cargo test-crate build
still references the absent `examples/_internal/regression/lambda_alpha_equivalence.lit`;
this checkpoint does not claim a full Cargo regression. Local receipts are
`eval-accepted`, `eval-focused`, `eval-related` and `eval-checkpoint` in the
existing compiler workspace.

Function, aggregate, matrix and algorithm evaluation certificates remain
unsupported, as do scalar operators outside the listed arithmetic slice.
For example, `eval abs(-3)` verifies in Litex but still rejects during Lean
compilation at `WD/Abs`, with no partial artifact. Work pauses after this
checkpoint at the maintainer's request.
