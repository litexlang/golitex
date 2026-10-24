# Litex-to-Lean coverage plan

Inventory totals were measured on 2026-10-23. The dated checkpoints below
record subsequent implementations and checks. Geo is outside this plan's
acceptance targets.

The current compiler already checks a useful combination of elementary
algebra, inequalities, sets, formula functions and named proofs. The next goal
is to expand this combination across the language by following its existing
statement, WD, verification and inference results.

## Coverage against the initial inventory

| Layer | Inventory | Existing compiler entrypoints | Remaining work |
| --- | ---: | ---: | --- |
| Statement forms | 52 | 37 at the checked coverage checkpoint | 15 forms remain outside that checkpoint; some require an explicit assumptions/model policy |
| Object constructors | 94 | 35 | 59 constructors remain outside the checked WD construction routes |
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

The checked 35 object entries comprise identifiers, calls, numeric literals,
standard sets and the imaginary-unit literal; add/subtract/negate/multiply/divide/power/absolute value; square
root; min/max/sign/floor/ceil; quotient/remainder/gcd/lcm/factorial; union/power set; finite enumeration/bounded builders/closed and half-open integer ranges/finite-sequence spaces;
cartesian products/tuples; and function sets/anonymous functions/function ranges. A formula
such as `f(g(x))` being supported does not imply support for the distinct
`Composition` object constructor.

All 15 number sets are represented: `N`, `Z`, `Q`, `R`, `C`, `N+`, `Q+`,
`R+`, `Z-`, `Q-`, `R-`, `Z*`, `Q*`, `R*`, and `C*`. Refined carriers use
bounded separation and retain ordinary membership, sign and nonzero facts.

The explicit adapters currently checked by Lean are
`tuple_equal_from_coordinates` (theorem release, finite-coordinate boundary),
`set_builder_member`, `defined_set_member`, `fn_set_member`, and
`cart_member_from_coordinates` (release and selected invocation).
Function membership currently accepts one/two-argument formula or cited
functions with alpha-equivalent complete domains; Cartesian membership uses
the retained finite-function shape. Other source/domain evidence variants still
reject explicitly. This count does not include automatic arithmetic rules.

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

`have fn outer(x R) R = fn(y R) R {x + y}(1)` still rejects at
`Function/BoundAnonymousCapture`. Its source verifies, but its literal
constructor needs the original enclosing-binder instantiation; the compiler
must not silently reuse it under a different raw binding.

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
rejection. The accepted source proof of `x+y<=4` on `[0,3) × [1,3)` currently
selects an unsupported builtin strategy; this increment does not replace that
route with a different Lean proof. This extends existing statement routes; it
does not change the preceding inventory baseline of **37/52 statement forms
and 35/94 object constructors**.

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
