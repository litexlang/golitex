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
| `N`, `Z`, `Q`, `R` and suffix subsets | Built-in number sets: naturals, integers, rationals, reals, and common subsets such as positive or nonzero values. | Membership facts such as `x $in R+` infer the corresponding ambient numeric membership. |
| Displayed finite sets `{a, b, c}` | A finite set containing the displayed elements. | Elements must be well-defined; finite-set facts and `finite_set_size` facts are inferred for displayed finite sets. |
| Set builders `{x S: P(x)}` | The subset of `S` whose elements satisfy the predicate in the builder. | The base set and predicate body must be well-defined under the bound variable assumptions. |
| `union(A, B)`, `intersect(A, B)`, `set_minus(A, B)`, `set_diff(A, B)` | Ordinary binary union, intersection, relative complement, and symmetric difference. | Arguments must be well-defined sets when set facts about the result are used. |
| `big_union(F)`, `big_intersect(F)` | Union and intersection over a family of sets. | Each operator takes exactly one well-defined family object. |
| `power_set(A)` | The set of all subsets of `A`. | `A` must be well-defined; proving `B $in power_set(A)` amounts to proving `B $subset A`. |
| `range(a, b)`, `closed_range(a, b)`, `a...b` | Integer-style ranges; `range` is half-open and `closed_range`/`...` are closed. | Endpoints must be integer-like where range enumeration facts are used. |
| Tuple `(a, b, ...)` | An ordered tuple with one-based projection syntax such as `(a, b)[1]`. | Coordinates must be well-defined. |
| `cart(A, B, ...)` | Cartesian product of the factor sets. | Factor objects must be well-defined sets; tuple membership checks each coordinate against its factor. |
| `fn(x S) T` | Function-space object from inputs in `S` to values in `T`, possibly with domain side conditions. | Parameter sets, side conditions, and return set must be well-defined. |
| Anonymous function `fn(x S) T {body}` | A function value written inline by binding `x` in `S` and returning `body`. | The body must be well-defined and must belong to `T` under the parameter and side-condition assumptions. |
| `fn_range(f)` | The image of a function over its declared domain. | `f` must be a supported function value. For an image restricted to `S`, use `fn_range(fn(x S) T {f(x)})`. |
| `seq(S)`, `finite_seq(S, n)` | Infinite positive-integer-indexed sequences and finite length-`n` sequences with values in `S`. | `S` must be a set; finite-sequence length must be positive and match literal length when a literal is used. |
| `matrix(S, r, c)` and matrix literals | Rectangular row-column indexed arrays with entries in `S`. | Row and column counts must be positive; literals must be rectangular and entries must belong to `S`. |
| `&StructName` and `&StructName{obj}.field` | Struct membership as a record-shaped tuple type, and explicit field access through a struct view. | Struct fields and equivalent facts must be well-defined; field access requires the object to belong to the selected struct. |
| `obj &StructName` in a binding, then `obj.field` or `obj.inner.field` (preview) | Select a default struct view with an explicit binding type, then follow consecutive fields declared directly with struct types. | The parser lowers every hop to an explicit struct view. It does not choose views from named definitions or known membership facts, and access after a call, index, or parenthesized expression requires an explicit `&Struct{expr}.field`. |
| `replacement(P, A)` | Replacement-style image set generated by a binary relation or predicate `P` over inputs from `A`. | `P` must be a binary prop/abstract prop and Litex must verify uniqueness of the output for each input. |

`$proper_subset` and `$proper_superset` are preview builtin predicates for
strict set inclusion.

Default struct views are also preview syntax. An explicit `obj &StructName`
binding selects that view; a directly struct-typed field supplies the next
view in a consecutive chain. A membership fact does not. Use the fully
explicit `&StructName{obj}.field` form to select another view at one access.

## Facts And Object Introduction

| Statement | Well-Definedness / Structural Checks | Truth Verification | Environment Effects |
|---|---|---|---|
| `fact` | The fact must be well-defined. | The fact must be verified as true. | Stores the fact and runs inference. |
| `trust` | Rejected in strict mode; each fact must be well-defined. | None. | Stores each fact as an unsafe assumption and runs inference. |
| `axiom name` | Rejected in strict mode; the `? forall ...` fact must be well-defined. | None. | Stores a named theorem-like `forall` fact for matching and `by thm`. |
| `trust have` | Rejected in strict mode; parameters are checked and bound; attached facts must be well-defined. | None for the attached facts. | Stores names, parameter type facts, attached facts, and inferred consequences. |
| `let a = x` (preview) | `a` must be unused and `x` must already be well-defined; exactly one name and one value are accepted. | None beyond checking the right-side object. | Stores the object name and the ordinary equality `a = x`; it declares no type or set membership. A later call through `a` may reuse already registered callable metadata from its stored equality class, while retaining ordinary arity and domain checks. |
| `have a R` | `a` must be unused; `R` must be a well-defined object. | Checks `R` is nonempty, for example `$is_nonempty_set(R)`. | Stores the object name `a`, stores `a $in R`, and runs inference. |
| `have a T = x` | Parameter count must match assigned objects; declared types are instantiated; `x` must be well-defined. | Verifies each assigned object satisfies its declared type. | Stores the object name, its type fact, `a = x`, and sequence or matrix value caches when relevant. |
| `obtain ... from exist` | Existential shape and parameter count must match the named witnesses. | Verifies the existential fact. | Stores witness names, witness type facts, instantiated body facts, and inference results. |
| `have ... by preimage` | Preimage count and function/range shape must match. | Verifies the source range membership. | Stores preimage names, source-domain facts, domain facts, and value equality facts. |
| `have fn = anonymous_fn` | Function body, function set, return set, and function name are checked. | Verifies the function value belongs to the return set. | Stores the function name, `f $in fn_set`, known function-body data, `f = anonymous_fn`, and inferred facts. |
| `have fn case_by_case` | Function set, cases, equal-to expressions, and function name are checked. | Verifies coverage of the declared domain, pairwise mutual exclusivity, and every return value's membership in the return set. | Stores the function name, function type, and generated case `forall` facts. |
| `have fn by induc` | Function and induction shapes are checked. | Proves the measure and lower bound are integer-valued, then verifies the lower bound, case partition, return values, and strict decrease of recursive calls. | Stores the function definition facts. |
| `have algo for f(...)` | `f` must already be a function; parameters and case shape are checked against it. | Verifies every executable return and case against the function facts. | Stores the checked implementation so later `eval f(...)` can use it. |
| `have fn ... by exist!` | The source `forall` must have the expected existence-uniqueness shape. | Verifies the source `forall` or the provided proof block. | Stores the function name, function type, property `forall`, and uniqueness fact. |
| `have tuple` | Name must be unused; dimension and coordinate-value expression must be well-defined. | Verifies `dimension $in N+` and `2 <= dimension`. | Stores tuple marker, dimension equality, and coordinate `forall` fact. |
| `have cart` | Name must be unused; dimension and coordinate-value expression must be well-defined. | Verifies `dimension $in N+` and `2 <= dimension`. | Stores set/cart markers, dimension equality, and projection `forall` fact. |
| `have seq` | Name must be unused; sequence set, anonymous function, and function set must be well-defined. | Verifies each generated value belongs to the return set. | Stores sequence membership, known function-body data, and equality to the anonymous function. |
| `have finite_seq` | Same checks as `have seq`, plus the bound must match the finite sequence length. | Verifies the bound is in `N+`, equals the declared length, and values are in the return set. | Stores finite-sequence membership, known function-body data, and equality to the anonymous function. |
| `have matrix` | Same checks as `have seq`, plus row and column bounds must match matrix dimensions. | Verifies row and column bounds are in `N+`, match declared dimensions, and values are in the return set. | Stores matrix membership, known function-body data, and equality to the anonymous function. |

## Definitions And Interfaces

| Statement | Well-Definedness / Structural Checks | Truth Verification | Environment Effects |
|---|---|---|---|
| `prop` | Parameters and `iff` facts must be well-defined; prop and abstract-prop names must not conflict. | Does not prove the `iff` facts. | Stores the concrete prop definition. |
| `abstract_prop` | Abstract-prop and concrete-prop names must not conflict. | None. | Stores the abstract prop definition. |
| `struct` | Parameter domains, field types, and equivalent facts must be well-defined; struct name must be unused. | Does not prove equivalent facts. | Stores the struct definition. |
| `template` | Template parameters and domains must be well-defined; the template body must execute in a local environment. | The body is verified according to ordinary executor behavior. | Stores the template definition. |
| `setting Name: ...` | Binder lines must come first, followed by optional shared-condition facts; the name must be unused. | None. Each `forall [Name]` or `forall [Name] => {...}` use elaborates to an ordinary universal fact, where normal well-definedness and proof checks apply. | Stores an elaboration-only parameter/domain bundle; every use receives fresh binder identities. |
| `have algo for f(...)` | Target function must exist; implementation parameters must match the function set. | Verifies every case implies the expected return; if there is no default return, verifies case coverage. | Stores the checked implementation. |
| `thm` | The theorem `forall` must be well-defined; the theorem name must be unique. | Executes the proof and verifies every then-clause. | Stores the theorem definition and stores the theorem `forall` fact. |
| `strategy` | The strategy `forall` must be well-defined; the strategy name must be unique. | Executes the proof and verifies every then-clause. | Stores the strategy definition, stores the strategy `forall` fact, and activates the strategy. |

## Proof Blocks

| Statement | Well-Definedness / Structural Checks | Truth Verification | Environment Effects |
|---|---|---|---|
| `claim` | The claimed fact must be well-defined. | Executes the proof and verifies the claimed target or then-clauses. | Stores the claimed fact and runs inference. |
| `witness` | Witness count and witness types must match the existential target. | Verifies the existential body under the proposed witnesses. | Stores the existential fact and runs inference. |
| `sketch` | Each nested statement performs its own checks in a child environment. | Nested statements verify normally. | No outer environment effect. |
| `try` | Rejects the `clear` control statement. Module imports are manifest declarations, not source statements. | Every nested statement must succeed and must not be unknown. | Commits the child environment into the parent environment. |

## By Statements

| Statement | Well-Definedness / Structural Checks | Truth Verification | Environment Effects |
|---|---|---|---|
| `by def fact` or `by def:` + `? fact` | A concrete positive prop call, or a supported positive builtin definition: subset/superset, proper subset/superset, injective/surjective/bijective, `fn_eq_in`, or `fn_eq`. | Explicitly runs the selected mathematical definition with the full verifier. Ordinary round-0 atomic verification may also try this direction before known `forall` facts and user strategies. | Stores the target and runs inference only after every requirement succeeds. |
| `by thm name(args)` | A user theorem must exist and accept the arguments. Reserved bare builtin theorem names instead validate their fixed target-object shape and arity. | Verifies user-theorem domains or the builtin handler's full-verifier requirements. One-layer builtin rules and structural builtin strategies are not unrestricted full-verifier entries. | Stores conclusions and runs inference only after every requirement succeeds; a failed builtin call stores nothing. |
| `by thm name(args) => atomic_fact` (preview) | The selected atomic fact must be well-defined in the parent context; the theorem call has the same checks as the legacy form. No indented body or compound target is accepted. | Applies the theorem in a temporary child scope, then checks the selected fact with the full atomic verifier there. The fact may be derived rather than a direct conclusion. | Discards the theorem's temporary conclusions, commits only the selected fact as the parent seed, then runs ordinary inference. Any failure commits nothing. |
| `by cases` | Then-facts must be well-defined; case/prove shape restrictions must hold. A zero-statement proof arm is written `case fact` without `:`. | Verifies cases cover all situations; each case, including a bodyless case, must prove every then-fact. | Stores the then-facts. |
| `by contra` | Target fact must be well-defined. | Assumes the negated target, runs the proof, and verifies both contradiction sides. | Stores the original target fact. |
| `by induc` | Induction source, parameter, and goal shapes must be valid. | Verifies base case and induction step. | Stores the generated concluding `forall` fact. |
| `by strong_induc` | Same structural checks as `by induc`, with the stronger induction-hypothesis shape. | Verifies base case and strong induction step. | Stores the generated concluding `forall` fact. |
| `by for forall ...` or `by for:` + `? forall ...` | The expanded finite/range domain and corresponding `forall` must be well-defined. Inline form accepts no indented proof body. | Verifies each assignment case. | Stores the generated corresponding `forall` fact. |
| `by enumerate finite_set forall ...` or its goal-block form | The finite-set expansion and corresponding `forall` must be well-defined. Inline form accepts no indented proof body. | Verifies every enumerated assignment case. | Stores the generated corresponding `forall` fact. |
| `by extension A = B` or `by extension:` + `? A = B` | Both set objects must be well-defined. Inline form accepts no indented proof body. | Verifies both subset directions. | Stores set equality. |
| `by enumerate range` | Membership fact and range endpoints must be well-defined; endpoints must be in `Z`. | Verifies membership and endpoint facts. | Stores the generated equality or disjunction of equalities. |
| `by closed_range as cases` | Membership fact and closed-range endpoints must be well-defined; endpoints must be in `Z`. | Verifies membership and endpoint facts. | Stores the generated equality or disjunction of equalities. |
| `by transitive_prop` | The prop must exist and be binary. | Proves the required transitivity `forall`. | Registers the prop as transitive. |
| `by symmetric_prop` | The prop must exist and have arity matching the `forall`. | Proves the required symmetry `forall`. | Registers the symmetric permutation. |
| `by reflexive_prop` | The prop must exist and be binary. | Proves the required reflexivity `forall`. | Registers the prop as reflexive. |
| `by antisymmetric_prop` | The prop must exist and be binary. | Proves the required antisymmetry `forall`. | Registers the prop as antisymmetric. |
| `by axiom_of_choice` | The family object must be well-defined. | Verifies the set-family and nonempty-member obligations. | Stores the choice-function existence conclusion. |
| `by zorn_lemma` | The set must be well-defined; the prop must exist and be binary. | Verifies nonempty, partial-order, and chain upper-bound obligations. | Stores the maximal-element existence conclusion. |
| `by regularity_axiom` | The set object must be well-defined. | Verifies the set is nonempty. | Stores the regularity/foundation conclusion. |

## Commands And Tools

| Statement | Well-Definedness / Structural Checks | Truth Verification | Environment Effects |
|---|---|---|---|
| `litex.config` | `[hierarchy]` declares `module` or `submodule`; only modules may use `[import]` and `[import std]`; `[export]` lists every direct child in recursive execution order. Imported targets must be external modules, exported folders must be submodules, and no configured child may be omitted. | None during discovery. | Declares imports, canonical folder/file namespaces, full `-r` traversal, and the `-f` prefix through a registered file. |
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
