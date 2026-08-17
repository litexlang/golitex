# Statement Execution Cheat Sheet

If you are new to Litex, read
[Litex Language Introduction](Litex_Language_Introduction.md) before this page.
That note explains the mathematical meaning of objects, facts, statements, and
context growth.  This cheat sheet is a dense executor/reference map.

For the complete language-level glossary -- 72 core object forms, 52 fact
forms, 64 statement forms, definitions, and the atomic verification loop -- read
[Litex System Map](Litex_System_Map.md).

This note summarizes the current executor behavior by separating each statement
into three parts:

- **Well-Definedness / Structural Checks**: parsing-adjacent runtime checks,
  name conflicts, shape checks, object well-definedness, parameter typing, and
  module or strategy lookup.
- **Truth Verification**: proof obligations where Litex must show that a fact
  follows from the current context.
- **Environment Effects**: changes committed to the active environment, module
  manager, caches, imported modules, or strategy tables.

This is a map of the current implementation, not a proposed redesign.

## Execution Pipeline Refactor Status

The executor is being migrated toward explicit three-stage helpers for each
statement:

1. `exec_XXX_stmt_verify_well_definedness`
2. `exec_XXX_stmt_verify_process`
3. `exec_XXX_stmt_affect_environment`

The explicit three-stage shape now covers control no-ops such as `do_nothing`
and `clear`, predicate definitions such as `prop` and `abstract_prop`, and the
object-introduction family of `have` statements listed below.

## Object Meaning Cheat Sheet

| Object form | Mathematical meaning | Typical well-definedness notes |
|---|---|---|
| Numeric literals and arithmetic expressions | Exact natural, integer, rational, or real number objects, with arithmetic interpreted in the usual numeric structure. | Operands must be numeric enough for the operation; division and remainder require nonzero divisors where relevant. |
| `N`, `Z`, `Q`, `R`, `C` and compact subsets | Built-in natural, integer, rational, real, and complex sets, with common positive, negative, or nonzero subsets. `C*` means the nonzero complex carrier. | Membership facts infer their ambient carrier and restriction; for example, `x $in C*` supplies `x $in C` and `x != 0`. |
| Displayed finite sets `{a, b, c}` | A finite set containing the displayed elements. | Elements must be well-defined; finite-set facts and `finite_set_size` facts are inferred for displayed finite sets. |
| Set builders `{x S: P(x)}` | The subset of `S` whose elements satisfy the predicate in the builder. | The base set and predicate body must be well-defined under the bound variable assumptions. |
| `union(A, B)`, `intersect(A, B)`, `set_minus(A, B)` | Ordinary binary union, intersection, and relative complement. Symmetric difference is `union(set_minus(A, B), set_minus(B, A))`. | Arguments must be well-defined sets when set facts about the result are used. |
| `big_union(F)`, `big_intersect(F)` | Union and intersection over a family of sets. | Each operator takes exactly one well-defined family object. |
| `power_set(A)` | The set of all subsets of `A`. | `A` must be well-defined; proving `B $in power_set(A)` amounts to proving `B $subset A`. |
| `range(a, b)`, `closed_range(a, b)`, `a...b` | Integer-style ranges; `range` is half-open and `closed_range`/`...` are closed. | Endpoints must be integer-like where range enumeration facts are used. Positive nonemptiness reduces to `a < b` for `range` and `a <= b` for `closed_range`. |
| Tuple `(a, b, ...)` | An ordered tuple with one-based projection syntax such as `(a, b)[1]`. | Coordinates must be well-defined. |
| `cart(A, B, ...)` | Cartesian product of the factor sets. | Factor objects must be well-defined sets; tuple membership checks each coordinate against its factor. |
| `fn(x S) T` | Function-space object from inputs in `S` to values in `T`, possibly with domain side conditions. | Parameter domains are read left to right, so later domains may cite earlier parameters. The return set may cite the function parameters and is instantiated with actual arguments at application. All resulting set expressions and side conditions must be well-defined. |
| Anonymous function `fn(x S) T {body}` | A function value written inline by binding `x` in `S` and returning `body`. | The body must be well-defined and must belong to `T` under the parameter and side-condition assumptions. |
| `sum(a, b, f)`, `product(a, b, f)`, and finite-set variants | A finite scalar aggregate of a unary iterand. | The iterand must be defined throughout the index domain and its declared return set must be provably contained in `C`; range forms also require integer `a <= b`. |
| `reduce(a, b, f, op, seed)` | An ascending left fold over the closed integer interval; an empty interval returns `seed`. | `op` must have homogeneous type `T x T -> T`, `f` must return `T`, and `seed` must be in `T`. Unlike range sum/product, `b < a` is valid. |
| `finite_set_reduce(S, f, op, seed)` | An order-independent fold over a finite set; the empty set returns `seed`. | In addition to the homogeneous carrier checks, `op` must be verified associative and commutative. Use an explicit enumeration plus `reduce` for order-sensitive operations. |
| Reduction bridges | Reuse existing aggregate, function, interval, and set interfaces. | Additive/zero and multiplicative/one reductions equal the corresponding sum/product. `$fn_eq_in` gives congruence; equal-length integer ranges admit order-preserving translation and endpoint unfolding; `$bijective` gives finite-set reindexing; adjacent ranges compose in order; disjoint unions compose by nesting one reduction as the other's seed. |
| `fn_range(f)` | The image of a function over its declared domain. | `f` must be a supported function value. For an image restricted to `S`, use `fn_range(fn(x S) T {f(x)})`. |
| `seq(S)`, `finite_seq(S, n)` | Infinite positive-integer-indexed sequences and finite length-`n` sequences with values in `S`. | `S` must be a set; `n` must be in `N` (so `n = 0` and `[]` are supported) and must match literal length when a literal is used. The function domain is exactly `closed_range(1, n)`. |
| `matrix(S, r, c)` and matrix literals | Rectangular row-column indexed arrays with entries in `S`. | Row and column counts must be positive; literals must be rectangular and entries must belong to `S`. |
| `&StructName` and `&StructName{obj}.field` | Struct membership as a record-shaped tuple type, and explicit field access through a struct view. | Struct fields must be well-defined. Equivalent facts are checked left to right, with earlier checked filters available to later well-definedness; field access requires the object to belong to the selected struct. A projected field may be called only when its declared carrier is a function set. |
| `obj &StructName` in a binding, then `obj.field` or `obj.inner.field` (preview) | Select a default struct view with an explicit binding type, then follow consecutive fields declared directly with struct types. | The parser lowers every hop to an explicit struct view. It does not choose views from named definitions or known membership facts, and access after a call, index, or parenthesized expression requires an explicit `&Struct{expr}.field`. |
| `unfold value` inside an argument list | Compile-time spread of a tuple into its coordinates or a struct value into all of its declared fields. | Struct fields follow declaration order; header parameters and equivalent facts are excluded. A named tuple needs a statically known arity, and a struct needs an explicit or default view. Ordinary argument checks still apply after expansion. |
| `replacement(P, A)` | Replacement-style image set generated by a binary relation or predicate `P` over inputs from `A`. | `P` must be a binary prop/abstract prop and Litex must verify uniqueness of the output for each input. |

`$proper_subset` and `$proper_superset` are preview builtin predicates for
strict set inclusion.

`$prime(p)` and `$coprime(a, b)` are reserved native predicates on `N` and
`N x N`, respectively. The latter is total on natural pairs, has arity two,
means `gcd(a,b)=1`, and is false at `(0,0)`. Arguments known only in `Z` or `R`
fail well-definedness for both predicates.

`$dvd(x, y)` is a preview native predicate on `Z x Z*`, in dividend-first
order. It means `x % y = 0` and exposes `exist a Z st {x = a * y}`; a zero
divisor is rejected at well-definedness.

Default struct views are also preview syntax. An explicit `obj &StructName`
binding selects that view; a directly struct-typed field supplies the next
view in a consecutive chain. A membership fact does not. Use the fully
explicit `&StructName{obj}.field` form to select another view at one access.

`unfold` is argument syntax rather than a runtime value. For example,
`consume(unfold G)` elaborates to the fields of `G` in the struct declaration's
current order, while `consume(unfold (a, b))` elaborates to `consume(a, b)`.
Use `unfold &StructName{G}` to select a view explicitly. Adding or reordering
struct fields therefore deliberately changes unfolded call signatures.

The fact grammar has a fixed hierarchy. `and` is a flat list of atomic facts;
`or` is the outer layer and collects atomic, chain, or completed flat-`and`
branches. Thus `and` binds more tightly than `or`; neither operator introduces
arbitrary recursive nesting.

A positive `forall` may use another `forall` as its sole direct conclusion.
This preview syntax is flattened before checking and storage by appending the
inner parameters and assumptions. A nested universal mixed with a sibling
conclusion is rejected rather than stored with changed empty-domain semantics.

Existential and set-builder bodies do not accept a `forall` entry. Their body
grammar stops at atomic facts, flat conjunctions, chains, and disjunctions.
Define a concrete `prop` whose clauses contain the universal fact, then place
the atomic `$P(args)` call in the body.

## Facts And Object Introduction

| Statement | Well-Definedness / Structural Checks | Truth Verification | Environment Effects |
|---|---|---|---|
| `fact` | The fact must be well-defined. | The fact must be verified as true. | Stores the fact and runs inference. |
| `trust` | Rejected in strict mode; each fact must be well-defined. Later facts in the statement may use earlier staged facts. | None. | Stages all facts and inference in a child environment, then commits the complete batch atomically; failure commits nothing from that statement. |
| `axiom name` | Rejected in strict mode; the `? forall ...` fact must be well-defined. | None. | Stores a named theorem-like `forall` fact for matching and `by thm`. |
| `trust have` | Rejected in strict mode; parameters are checked and bound; attached facts must be well-defined. | None for the attached facts. | Stages names, parameter type facts, attached facts, and inference together, then commits them atomically; failure releases none of them. |
| `let a = x` (preview) | `a` must be unused and `x` must already be well-defined; exactly one name and one value are accepted. | None beyond checking the right-side object. | Stores the object name and the ordinary equality `a = x`; it declares no type or set membership. A later call through `a` may reuse already registered callable metadata from its stored equality class, while retaining ordinary arity and domain checks. |
| `have a R` | `a` must be unused; `R` must be a well-defined object. | Checks `R` is nonempty, for example `$is_nonempty_set(R)`. | Stores the object name `a`, stores `a $in R`, and runs inference. |
| `have a T = x` | Parameter count must match assigned objects; declared types are instantiated; `x` must be well-defined. | Verifies each assigned object satisfies its declared type during `verify_process`; a mismatch reports required and known standard numeric carriers when available. | Stores the object name, its type fact, `a = x`, and sequence or matrix value caches when relevant; a failed carrier check stores nothing. |
| `obtain ... from exist ...` or `obtain ... from $P(args)` | Existential shape and parameter count must match the named witnesses. The prop form requires one concrete definition clause whose outer form is positive `exist` or `exist!`, then substitutes `args`. | Verifies the direct existential or the source prop fact. | Stores witness names, witness type facts, instantiated body facts, and inference results. Positive `exist` prop sources compile through a checked definition projection followed by ordinary existential elimination. |
| `obtain ... from thm name(args)` | The theorem call must resolve and have exactly one direct positive `exist`/`exist!` conclusion; witness count must match. | Runs the same argument, domain, and builtin-requirement checks as `by thm` in a temporary scope, then eliminates that exact conclusion. | Discards the intermediate theorem conclusion; stores witness names, types, body facts, inference, and `exist!` uniqueness. The combined form currently fails closed in Litex-to-Lean. |
| `have ... by preimage` | Preimage count and function/range shape must match. | Verifies the source range membership. | Stores preimage names, source-domain facts, domain facts, and value equality facts. |
| `have fn = anonymous_fn` | Function body, function set, return set, and function name are checked. | Verifies the function value belongs to the return set. | Stores the function name, `f $in fn_set`, known function-body data, `f = anonymous_fn`, and inferred facts. |
| `have fn case_by_case` | Function set, cases, equal-to expressions, and function name are checked. | Verifies coverage of the declared domain, pairwise mutual exclusivity, and every return value's membership in the return set. | Stores the function name, function type, and generated case `forall` facts. |
| `have fn by induc` | Function and induction shapes are checked. | Proves the measure and lower bound are integer-valued, then verifies the lower bound, case partition, return values, and strict decrease of recursive calls. | Stores the function definition facts. |
| `have algo for f(...)` | `f` must already be a function; parameters and case shape are checked against it. | Verifies every executable return and case against the function facts. | Stores the checked implementation so later `eval f(...)` can use it. |
| `have fn ... by exist!` | The source `forall` must have the expected existence-uniqueness shape. | Verifies the source `forall` or the provided proof block. | Stores the function name, function type, property `forall`, and uniqueness fact. |
| `have tuple` | Name must be unused; dimension and coordinate-value expression must be well-defined. | Verifies `dimension $in N+` and `2 <= dimension`. | Stores tuple marker, dimension equality, and coordinate `forall` fact. |
| `have cart` | Name must be unused; dimension and coordinate-value expression must be well-defined. | Verifies `dimension $in N+` and `2 <= dimension`. | Stores set/cart markers, dimension equality, and projection `forall` fact. |
| `have seq` | Name must be unused; sequence set, anonymous function, and function set must be well-defined. | Verifies each generated value belongs to the return set. | Stores sequence membership, known function-body data, and equality to the anonymous function. |
| `have finite_seq` | Same checks as `have seq`, plus the bound must match the finite sequence length. | The indexed-definition form verifies a positive bound, equality to the declared length, and values in the return set; use the literal `[]` for the zero-length value. | Stores finite-sequence membership, known function-body data, and equality to the anonymous function. |
| `have matrix` | Same checks as `have seq`, plus row and column bounds must match matrix dimensions. | Verifies row and column bounds are in `N+`, match declared dimensions, and values are in the return set. | Stores matrix membership, known function-body data, and equality to the anonymous function. |

## Definitions And Interfaces

| Statement | Well-Definedness / Structural Checks | Truth Verification | Environment Effects |
|---|---|---|---|
| `prop` | Parameters and `iff` facts must be well-defined; prop and abstract-prop names must not conflict. | Does not prove the `iff` facts. | Stores the concrete prop definition. |
| `abstract_prop` | Abstract-prop and concrete-prop names must not conflict. | None. | Stores the abstract prop definition. |
| `struct` | Parameter domains and field types must be well-defined; equivalent facts are checked left to right in a temporary field scope and earlier checked facts may justify later well-definedness; struct name must be unused. | Does not prove equivalent facts. | Stores the struct definition only after the complete check succeeds. |
| `template` | Template parameters and domains must be well-defined; the template body must execute in a local environment. | The body is verified according to ordinary executor behavior. | Stores the template definition. |
| `setting Name: ...` | Binder lines must come first, followed by optional shared-condition facts; the name must be unused. | None. Each `forall [Name]` or `forall [Name] => fact` use elaborates to an ordinary universal fact, where normal well-definedness and proof checks apply. | Stores an elaboration-only parameter/domain bundle; every use receives fresh binder identities. |
| `have algo for f(...)` | Target function must exist; implementation parameters must match the function set. | Verifies every case implies the expected return; if there is no default return, verifies case coverage. | Stores the checked implementation. |
| `thm` | The theorem `forall` must be well-defined; the theorem name must be unique. | Executes the proof and verifies every then-clause. | Stores the theorem definition and stores the theorem `forall` fact. |
| `strategy` | The strategy `forall` must be well-defined; the strategy name must be unique. | Executes the proof and verifies every then-clause. | Stores the strategy definition, stores the strategy `forall` fact, and activates the strategy. |

## Proof Blocks

| Statement | Well-Definedness / Structural Checks | Truth Verification | Environment Effects |
|---|---|---|---|
| `claim` | The claimed fact must be well-defined. | Executes the proof and verifies the claimed target or then-clauses. | Stores the claimed fact and runs inference. |
| `witness` | Witness count and witness types must match the existential target. The `$P(args)` form requires one concrete positive ordinary `exist` definition clause; use explicit `witness exist! ...` plus `by def` for unique existence. | Verifies the existential body under the proposed witnesses; explicit `exist!` also verifies the generated uniqueness `forall`. | Stores the direct existential or the named atomic fact and runs inference. |
| `sketch` | Each nested statement performs its own checks in a child environment. | Nested statements verify normally. | No outer environment effect. |
| `try` | Rejects the `clear` control statement. Module imports are manifest declarations, not source statements. | Every nested statement must succeed and must not be unknown. | Commits the child environment into the parent environment. |

## Goal-Shape Routing Table

Use this table before expanding a proof manually. It is organized by the fact
you need next, rather than by parser keyword. The default search order is:
reuse a known fact, try one direct builtin consequence, choose the matching
native proof surface, cite an existing mathematical interface, and only then
write a manual proof.

First distinguish data from facts. If later code must cite a value, introduce
it with `have`; if it must apply `f(x)`, use `have fn`; if it asserts
`$P(x)`, define a `prop`; if it should visibly cite a stable mathematical
result, use `thm`. `claim` is for a nearby derived fact, not a substitute for
an object or reusable function. See [Facts And Object Introduction](#facts-and-object-introduction)
and [Definitions And Interfaces](#definitions-and-interfaces) for their exact
execution contracts.

<!-- BEGIN GENERATED GOAL-SHAPE ROUTES -->
| Goal shape | Fact kind | Required known leaves | Supported direction | Try first | Nearest rejected or over-expanded shape | Executable evidence |
|---|---|---|---|---|---|---|
| An atomic arithmetic, carrier, membership, equality, or order consequence already supported by context | Direct fact / one-layer builtin | The exact operands, carrier facts, and any immediate premise required by that rule | Construct the requested atomic fact | State the fact directly | Adding a wrapper `claim` or `thm` around a fact the verifier already knows | [`fundamental_comparison_builtin_rules.lit`](../examples/02_builtin_math/fundamental_comparison_builtin_rules.lit) |
| A positive concrete predicate call whose definition body is already proved | Definition introduction | The instantiated definition clauses and well-defined arguments | Body facts to named positive predicate | `by def $P(args)` | Bare `by def` on equality, a negative predicate goal, or the placeholder `by def:` form when no nested proof is needed | [`by_definition.lit`](../examples/01_proof_patterns/by_definition.lit), [`inline_by_definition.lit`](../examples/01_proof_patterns/inline_by_definition.lit) |
| A result supplied by a named user theorem | Named mathematical interface | The theorem's domain requirements and arguments | Theorem premises to its stored conclusions, or to one selected atomic consequence | `by thm name(args)` or `by thm name(args) => fact` | Expecting a theorem call inside bare `forall` conclusion syntax, or selecting a compound target | [`by_theorem_selected_fact.lit`](../examples/01_proof_patterns/by_theorem_selected_fact.lit) |
| A set-builder, tuple, Cartesian product, function-set, iterated-object, or canonical rational-fraction conclusion whose reserved interface has compound requirements | Explicit builtin theorem interface | The interface-specific full-verifier requirements, such as builder predicate, every coordinate equality, pointwise order, or rational membership | Requirements to one constructed atomic fact, or to the fixed unique-existence fact for `rational_has_unique_reduced_fraction(q)` | Bare reserved `by thm set_builder_member(...)`, `tuple_equal_from_coordinates(...)`, `rational_has_unique_reduced_fraction(q)`, or the matching iterated-object interface | Expecting a one-layer atomic builtin to synthesize an arbitrary quantified premise; qualifying a reserved builtin name | [`rational_reduced_fraction_builtin_theorem.lit`](../examples/01_proof_patterns/rational_reduced_fraction_builtin_theorem.lit), [`generic_cart_member_coordinates.lit`](../examples/_internal/regression/generic_cart_member_coordinates.lit), [`builtin_interfaces.rs`](../src/main_test/lit_file_runner_tests/runtime_regression_tests/builtin_interfaces.rs) |
| Equality of two sets | Extensional proof | Well-defined set objects and both membership directions | Mutual subset facts to set equality | `by extension A = B` or goal-block `by extension:` | Syntactic normalization of unrelated construction histories, or using set extensionality for functions | [`inline_by_proof_methods.lit`](../examples/01_proof_patterns/inline_by_proof_methods.lit) |
| A universal fact over displayed finite sets | Finite enumeration | Every quantified domain must be concretely enumerable | All concrete assignments to the universal fact | `by enumerate finite_set` | Enumeration over `N`, an opaque set, or another domain with no concrete finite expansion | [`bodyless_by_goal_blocks.lit`](../examples/01_proof_patterns/bodyless_by_goal_blocks.lit), [`enumerate_finite_set.lit`](../examples/_internal/regression/enumerate_finite_set.lit) |
| Equality alternatives for a known integer member of `range` or `closed_range` | Bounded range classification | Integer endpoints and enough carrier/order facts to verify membership | Range membership to one equality or a flat disjunction of equalities | `by enumerate range` / `by enumerate closed_range` | A nested numeric boundary-case ladder; arbitrary-set or unbounded enumeration | [`bounded_range_classification.lit`](../examples/01_proof_patterns/bounded_range_classification.lit) |
| A universal fact over an integer range or supported finite Cartesian product | Bounded universal proof | A supported finite/range domain and a well-defined universal target | Each generated assignment to the universal fact | `by for` | Treating `by for` as unbounded quantifier automation | [`inline_by_proof_methods.lit`](../examples/01_proof_patterns/inline_by_proof_methods.lit) |
| A goal under an available disjunction or generated alternatives | Case proof | The matching disjunction or exhaustive alternatives must already be known | Every covered branch to the same target | `by cases` | Inventing cases with no known exhaustive source; writing `case fact:` with an empty body instead of bodyless `case fact` | [`bodyless_by_cases.lit`](../examples/01_proof_patterns/bodyless_by_cases.lit) |
| A negative or contradiction-shaped goal | Contradiction proof | A well-defined target and facts that yield both sides of a contradiction | Negated target assumption to the original target | `by contra` | A bare `impossible` with no contradictory pair; unlike other bodyless routes, omitting the final `impossible` | [`bodyless_by_goal_blocks.lit`](../examples/01_proof_patterns/bodyless_by_goal_blocks.lit) |
| A discrete natural/integer or finite-set invariant | Inductive proof | Supported induction parameter, base, and invariant shape | Base plus successor/insertion step to the generated universal fact | `by induc` / `by strong_induc` | Induction over an arbitrary real or an invariant that has not been packaged in the required goal shape | [`bodyless_by_goal_blocks.lit`](../examples/01_proof_patterns/bodyless_by_goal_blocks.lit), [`finite_set_induction.lit`](../examples/_internal/regression/finite_set_induction.lit) |
| A bare universal statement needs proof-control commands such as cases, theorem calls, witnesses, or induction | Local proved fact | The complete universal target must be well-defined | Local proof body to one stored fact | Wrap the target in `claim:` or name it with `thm` when reusable | Putting `by thm`, `by def`, or another proof-control statement directly in a bare `forall ... =>:` conclusion list | [`bodyless_by_goal_blocks.lit`](../examples/01_proof_patterns/bodyless_by_goal_blocks.lit) |
<!-- END GENERATED GOAL-SHAPE ROUTES -->

The table is generated from [`goal_shape_routes.json`](goal_shape_routes.json).
After editing that data, run
`python3 tools/generate_goal_shape_routing.py --write`; CI uses the same command
with `--check` to reject stale rows or missing evidence files.

These routes are directional. For example, known set-builder membership can
expose its base and predicate facts automatically, while constructing that
membership from the base and predicate uses the explicit
`set_builder_member` interface. Likewise, a case equality may still need one
explicit substituted atomic equality before the verifier can rewrite through a
compound expression; the range-classification example records that boundary.

When the proof action is known but the input object is still unusable, continue
with the [Object Proof Playbook](Object_Proof_Playbook.md). Its construction-
before-consumption rules cover exact carriers, set-valued functions, finite
aggregates, dependent field projection, tuple reconstruction, and recursive
indices.

## By Statements

For every `by ...:` goal-block route, ordinary proof statements after the `?`
goals are optional; an empty list still runs the route's final verifier and
cannot admit an unproved target. Required structural arms remain, and
`by contra` uniquely requires a final explicit `impossible fact`.

| Statement | Well-Definedness / Structural Checks | Truth Verification | Environment Effects |
|---|---|---|---|
| `by def fact` | A concrete positive prop call, or a supported positive builtin definition: subset/superset, proper subset/superset, `$prime`, `$coprime`, `$dvd`, injective/surjective/bijective, `fn_eq_in`, or `fn_eq`. | Explicitly runs the selected mathematical definition with the full verifier. Ordinary round-0 atomic verification may also try this direction before known `forall` facts and user strategies. | Stores the target and runs inference only after every requirement succeeds. |
| `by thm name(args)` | A user theorem must exist and accept the arguments. Reserved bare builtin theorem names instead validate their fixed target-object shape and arity. `rational_has_unique_reduced_fraction(q)` has arity one and requires `q $in Q`. | Verifies user-theorem domains or the builtin handler's explicit requirements. The rational handler checks membership in `Q`, constructs its fixed conclusion, and verifies that conclusion is well-defined; the same existential is not an implicit builtin fact. One-layer builtin rules and structural builtin strategies are not unrestricted full-verifier entries. | Stores conclusions and runs inference only after every requirement succeeds; the rational interface stores `exist! p Z, d N+ st {q = p / d, gcd(p, d) = 1}`. A failed builtin call stores nothing. |
| `by thm name(args) => atomic_fact`, or `by thm name(args):` plus one `? atomic_fact` goal (preview) | The selected atomic fact must be well-defined in the parent context; the theorem call has the same checks as the legacy form. The goal-block spelling is bodyless, and neither spelling accepts a compound target. | Applies the theorem in a temporary child scope, then checks the selected fact with the full atomic verifier there. The fact may be derived rather than a direct conclusion. | Discards the theorem's temporary conclusions, commits only the selected fact as the parent seed, then runs ordinary inference. Any failure commits nothing. |
| `by cases` | Then-facts must be well-defined; case/prove shape restrictions must hold. A zero-statement proof arm is written `case fact` without `:`. | Verifies cases cover all situations; each case, including a bodyless case, must prove every then-fact. | Stores the then-facts. |
| `by contra` | Target fact must be well-defined. | Assumes the negated target, runs the proof, and verifies both contradiction sides. | Stores the original target fact. |
| `by induc` | Induction source, parameter, and goal shapes must be valid. | Verifies base case and induction step. | Stores the generated concluding `forall` fact. |
| `by strong_induc` | Same structural checks as `by induc`, with the stronger induction-hypothesis shape. | Verifies base case and strong induction step. | Stores the generated concluding `forall` fact. |
| `by for:` + `? forall ...` | The expanded finite/range domain and corresponding `forall` must be well-defined. | Verifies each assignment case. | Stores the generated corresponding `forall` fact. |
| `by enumerate finite_set:` + `? forall ...` | The finite-set expansion and corresponding `forall` must be well-defined. | Verifies every enumerated assignment case. | Stores the generated corresponding `forall` fact. |
| `by extension A = B` or `by extension:` + `? A = B` | Both set objects must be well-defined. Inline form accepts no indented proof body. | Verifies both subset directions. | Stores set equality. |
| `by enumerate range` | Membership fact and range endpoints must be well-defined; endpoints must be in `Z`. | Verifies membership and endpoint facts. | Stores the generated equality or disjunction of equalities. |
| `by closed_range as cases` | Membership fact and closed-range endpoints must be well-defined; endpoints must be in `Z`. | Verifies membership and endpoint facts. | Stores the generated equality or disjunction of equalities. |
| `by transitive_prop` | The prop must exist and be binary. | Proves the required transitivity `forall`. | Registers the prop as transitive. |
| `by symmetric_prop` | The prop must exist and have arity matching the `forall`. | Proves the required symmetry `forall`. | Registers the symmetric permutation. |
| `by reflexive_prop` | The prop must exist and be binary. | Proves the required reflexivity `forall`. | Registers the prop as reflexive. |
| `by antisymmetric_prop` | The prop must exist and be binary. | Proves the required antisymmetry `forall`. | Registers the prop as antisymmetric. |
| `by axiom_of_choice: set S: ...` | `S` is a set. | Proves every `A $in S` is nonempty. | Stores `exist f fn(A S)big_union(S) st {$is_choice_function_for(S,S,fn(A S)S {A},f)}`. |
| `by zorn_lemma: set S, prop P, prop U, prop M: ...` | `P` is binary; `U(c power_set(S),u S)` and `M(m S)` are concrete props with the exact upper-bound and maximality definitions. | Proves nonemptiness, partial-order laws, and a named upper-bound witness for every chain. | Stores `exist m S st {$M(m)}`; no existential body contains an anonymous `forall`. |
| `by regularity_axiom` | The set object must be well-defined. | Verifies the set is nonempty. | Stores the regularity/foundation conclusion. |

## Commands And Tools

| Statement | Well-Definedness / Structural Checks | Truth Verification | Environment Effects |
|---|---|---|---|
| `litex.config` | `[hierarchy]` declares `module` or `submodule`; only modules may use `[import]` and `[import std]`; `[export]` lists every direct child in recursive execution order. Optional `[allow bare export]`, `[allow bare import std]`, and `[allow bare import]` entries must name items in their matching tables; allow-bare exports must be folders. | None during discovery. Enabled, loaded sources must expose a unique recursive public terminal-symbol set; different symbols with one bare name are a config error. | Declares imports, canonical folder/file namespaces, full `-r` traversal, and the `-f` prefix. A source gets one inherited bare-symbol index; explicit qualified names and fields bypass it, private imports and isolated imports stay qualified-only, and active external names cannot be rebound locally. |
| `clear` | None. | None. | Clears the current user environment; imported modules stay registered and active. |
| `do_nothing` | None. | None. | None. |
| `eval` | The expression must be evaluable, or a name with a known executable definition. | Does not separately prove the original expression; it stores the evaluation equality. | Stores and reports `expr = value` with evaluation-result reason. |
| `use strategy` | The strategy must exist. | None. | Activates the strategy. |
| `stop strategy` | The strategy must exist. | None. | Stops the strategy for its target atomic-fact key. |

## Example: `have a R`

The statement:

```litex
have a R
```

has this executor shape:

1. **Well-Definedness / Structural Checks**: `a` must not already be bound in
   the current scope, and `R` must be a well-defined object.
2. **Truth Verification**: Litex verifies that `R` is nonempty, usually through
   a fact like `$is_nonempty_set(R)`.
3. **Environment Effects**: Litex binds a new object named `a`, stores
   `a $in R`, updates caches, and runs inference.
