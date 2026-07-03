# Statement Execution Cheat Sheet

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

## Common Building Blocks

| Operation | Well-Definedness / Structural Checks | Truth Verification | Environment Effects |
|---|---|---|---|
| `define_params_with_type` | Checks each parameter type is well-defined; optionally checks the type is nonempty; checks each name is not already bound. | The optional nonempty check is a truth verification, for example `$is_nonempty_set(R)`. | Stores each identifier and its type fact, then runs inference. |
| `define_params_with_set` | Checks the set object is well-defined; checks each name is not already bound. | No extra truth proof beyond storing the generated membership fact through the normal store path. | Stores each identifier and its in-set fact, then runs inference. |
| `verify_well_defined_and_store_and_infer` | Checks the fact is well-defined. | Does not prove the fact is true. | Stores the fact, updates known-fact caches, and runs inference. |
| `store_*_without_well_defined_verified_*` | Assumes required well-definedness was already checked by the caller. | Does not prove the fact is true. | Stores the fact and runs inference. |
| Ordinary fact execution | Checks the fact is well-defined during the store phase. | Proves the fact first. | Stores the fact and inferred consequences. |

## Facts And Object Introduction

| Statement | Well-Definedness / Structural Checks | Truth Verification | Environment Effects |
|---|---|---|---|
| `fact` | The fact must be well-defined. | The fact must be verified as true. | Stores the fact and runs inference. |
| `know` | Rejected in strict mode; each fact must be well-defined. | None. | Stores each fact as an unsafe assumption and runs inference. |
| `let` | Rejected in strict mode; parameters are checked and bound; attached facts must be well-defined. | None for the attached facts. | Stores names, parameter type facts, attached facts, and inferred consequences. |
| `have a R` | `a` must be unused; `R` must be a well-defined object. | Checks `R` is nonempty, for example `$is_nonempty_set(R)`. | Stores the object name `a`, stores `a $in R`, and runs inference. |
| `have a T = x` | Parameter count must match assigned objects; declared types are instantiated; `x` must be well-defined. | Verifies each assigned object satisfies its declared type. | Stores the object name, its type fact, `a = x`, and sequence or matrix value caches when relevant. |
| `have ... by exist` | Existential shape and parameter count must match the named witnesses. | Verifies the existential fact. | Stores witness names, witness type facts, instantiated body facts, and inference results. |
| `have ... by preimage` | Preimage count and function/range shape must match. | Verifies the source range membership. | Stores preimage names, source-domain facts, domain facts, and value equality facts. |
| `have fn = anonymous_fn` | Function body, function set, return set, and function name are checked. | Verifies the function value belongs to the return set. | Stores the function name, `f $in fn_set`, known function-body data, `f = anonymous_fn`, and inferred facts. |
| `have fn case_by_case` | Function set, cases, equal-to expressions, and function name are checked. | Verifies case return values and related case obligations. | Stores the function name, function type, and generated case `forall` facts. |
| `have fn by induc` | Function and induction shapes are checked. | Verifies base and step obligations. | Stores the function definition facts. |
| `have fn by forall exist unique` | The source `forall` must have the expected existence-uniqueness shape. | Verifies the source `forall` or the provided proof block. | Stores the function name, function type, property `forall`, and uniqueness fact. |
| `have tuple` | Name must be unused; dimension and coordinate-value expression must be well-defined. | Verifies `dimension $in N_pos` and `2 <= dimension`. | Stores tuple marker, dimension equality, and coordinate `forall` fact. |
| `have cart` | Name must be unused; dimension and coordinate-value expression must be well-defined. | Verifies `dimension $in N_pos` and `2 <= dimension`. | Stores set/cart markers, dimension equality, and projection `forall` fact. |
| `have seq` | Name must be unused; sequence set, anonymous function, and function set must be well-defined. | Verifies each generated value belongs to the return set. | Stores sequence membership, known function-body data, and equality to the anonymous function. |
| `have finite_seq` | Same checks as `have seq`, plus the bound must match the finite sequence length. | Verifies the bound is in `N_pos`, equals the declared length, and values are in the return set. | Stores finite-sequence membership, known function-body data, and equality to the anonymous function. |
| `have matrix` | Same checks as `have seq`, plus row and column bounds must match matrix dimensions. | Verifies row and column bounds are in `N_pos`, match declared dimensions, and values are in the return set. | Stores matrix membership, known function-body data, and equality to the anonymous function. |

## Definitions And Interfaces

| Statement | Well-Definedness / Structural Checks | Truth Verification | Environment Effects |
|---|---|---|---|
| `prop` | Parameters and `iff` facts must be well-defined; prop and abstract-prop names must not conflict. | Does not prove the `iff` facts. | Stores the concrete prop definition. |
| `abstract_prop` | Abstract-prop and concrete-prop names must not conflict. | None. | Stores the abstract prop definition. |
| `struct` | Parameter domains, field types, and equivalent facts must be well-defined; struct name must be unused. | Does not prove equivalent facts. | Stores the struct definition. |
| `template` | Template parameters and domains must be well-defined; the template body must execute in a local environment. | The body is verified according to ordinary executor behavior. | Stores the template definition. |
| `algo` | Target function must exist; algorithm parameters must match the function set. | Verifies every case implies the expected return; if there is no default return, verifies case coverage. | Stores the algorithm definition. |
| `thm` | The theorem `forall` must be well-defined; theorem names must be unique. | Executes the proof and verifies every then-clause. | Stores the theorem definition and stores the theorem `forall` fact. |
| `strategy` | The strategy `forall` must be well-defined; strategy names must be unique. | Executes the proof and verifies every then-clause. | Stores the strategy definition, stores the strategy `forall` fact, and activates the strategy. |
| `alias prop` | Target prop must exist and must be concrete, not abstract; alias name must be storable. | None. | Stores a copied prop definition under the new name. |
| `alias thm` | Target theorem must exist; alias name must be storable. | None. | Stores a copied theorem definition under the new name. |

## Proof Blocks

| Statement | Well-Definedness / Structural Checks | Truth Verification | Environment Effects |
|---|---|---|---|
| `claim` | The claimed fact must be well-defined. | Executes the proof and verifies the claimed target or then-clauses. | Stores the claimed fact and runs inference. |
| `sketch` | Each nested statement performs its own checks in a child environment. | Nested statements verify normally. | No outer environment effect. |
| `try` | Rejects control statements such as `clear`, `import`, `run_file`, and `stop import`. | Every nested statement must succeed and must not be unknown. | Commits the child environment into the parent environment. |

## By Statements

| Statement | Well-Definedness / Structural Checks | Truth Verification | Environment Effects |
|---|---|---|---|
| `by thm` | The theorem must exist; arguments must satisfy theorem parameter types. | Verifies instantiated theorem domain facts. | Stores instantiated then-facts and runs inference. |
| `by cases` | Then-facts must be well-defined; case/prove shape restrictions must hold. | Verifies cases cover all situations; each case proof must prove the then-facts. | Stores the then-facts. |
| `by contra` | Target fact must be well-defined. | Assumes the negated target, runs the proof, and verifies both contradiction sides. | Stores the original target fact. |
| `by induc` | Induction source, parameter, and goal shapes must be valid. | Verifies base case and induction step. | Stores the generated concluding `forall` fact. |
| `by strong_induc` | Same structural checks as `by induc`, with the stronger induction-hypothesis shape. | Verifies base case and strong induction step. | Stores the generated concluding `forall` fact. |
| `by for` | The expanded finite/range domain and corresponding `forall` must be well-defined. | Verifies each assignment case. | Stores the generated corresponding `forall` fact. |
| `by enumerate finite_set` | The finite-set expansion and corresponding `forall` must be well-defined. | Verifies every enumerated assignment case. | Stores the generated corresponding `forall` fact. |
| `by extension` | Both set objects must be well-defined. | Verifies both subset directions. | Stores set equality. |
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
| `import` | Resolves module path/name; checks aliases, cycles, duplicate module names, and duplicate paths. | Runs the imported module normally when it is not already cached. | Registers the module environment, import dependencies, and reactivates cached modules when applicable. |
| `run_file` | Resolves and reads the file path. | Runs the target file normally. | Executes directly in the current user environment. |
| `clear` | None. | None. | Clears the current user environment and stops all imported modules. |
| `stop import` | The module must already be imported. | None. | Marks the module as stopped for automatic verification. |
| `do_nothing` | None. | None. | None. |
| `eval` | The object must be evaluable. | Does not separately prove the original expression; it stores the evaluation equality. | Stores `expr = value` with evaluation reason. |
| `eval by` | The left and right objects must be well-defined. | Verifies `lhs = rhs`. | Stores `lhs = rhs`, `rhs = value`, and `lhs = value`. |
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
