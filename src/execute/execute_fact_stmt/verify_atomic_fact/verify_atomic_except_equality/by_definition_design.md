# ByDefinition: builtin prop vs user `prop`

Status: **current** (preview).

Canonical note for ambient / `by def` definition expansion of positive atomic
predicates.

## Owners

| Area | Path |
|------|------|
| Fork dispatcher | `search_atomic_except_equality_fact_proof_by_definition.rs` |
| Builtin expanders | `builtin_prop_definition.rs` |
| Result types | `result.rs` (`AtomicExceptEqualityFactSearchProofByDefinition`, `BuiltinPropDefinitionProof`) |
| Manual preview | `docs/Manual.md` (`by def` / ByDefinition) |
| Proof-node tracers | `examples/proof_nodes/atomic/by_definition/` |
| Unit gate | `src/execute/exec_stmt_transaction_tests.rs` (`builtin_prop_by_definition_*`) |

## Decision

Builtin predicates with an **official definition** are not algebraic
`ByBuiltinRule` slots. They share the **ByDefinition** stage with user `prop`:

1. Try builtin official-definition expansion.
2. Else try user `prop` definition expansion.

Rationale: `$subset`, `$prime`, … are definitional interfaces.
Expanding them to obligation facts keeps ambient search and statement `by def`
on one path, with typed evidence per predicate.

**AST shape:** each official builtin is a **dedicated `AtomicFact` variant**
(`ProperSubsetFact`, `PrimeFact`, `CoprimeFact`, `DvdFact`, `InjectiveFact`,
`SurjectiveFact`, `BijectiveFact`, `IsChoiceFunctionForFact`, and their `Not*`
twins). `NormalAtomicFact` / `NotNormalAtomicFact` are **user-defined
`$prop(...)` only** — they are not used for these builtins.
## Evidence shape

**One builtin predicate ↔ one dedicated proof struct** under
`BuiltinPropDefinitionProof` (no shared payload + tag enum).

Each struct carries `requirement_facts` and `proof_of_requirement_facts`.

## Official definition table

| Surface | Obligations (sketch) |
|---------|----------------------|
| `A $subset B` | `forall x A: x $in B` |
| `A $superset B` | `forall x B: x $in A` |
| `$proper_subset(A, B)` / infix `A $proper_subset B` | `A $subset B` and `A != B` |
| `$proper_superset(A, B)` / infix `A $proper_superset B` | `B $subset A` and `A != B` |
| `$injective(A, B, f)` | injectivity forall |
| `$surjective(A, B, f)` | surjectivity forall/exist |
| `$bijective(A, B, f)` | injective and surjective |
| `$is_choice_function_for(I, S, g, f)` | `forall alpha I: f(alpha) $in g(alpha)` |
| `$prime(p)` | `2 <= p` and trial-divisor forall on `range(2, p)` |
| `$coprime(a, b)` | `(a != 0 or b != 0)` and `gcd(a, b) = 1` |
| `$dvd(x, y)` | `x % y = 0` and `exist a Z: x = a * y` |

`$proper_*` may be written **prefix** `$proper_subset(A, B)` or **infix**
`A $proper_subset B` (binary `$` atomics).

## Explicit non-goals

### Finite list-set inclusion uses the forall definition

`{1} $subset {1, 2}` expands to `forall x {1}: x $in {1, 2}`. The request succeeds when the ordinary verifier proves that forall.
`by enumerate finite_set` remains an alternative explicit finite proof.

### Mapping / prime / choice may need prior facts

`by def` only rechecks definition obligations. Soft miss is correct when those
obligations are not yet proved. Do not fake them with `trust` inside
`examples/proof_nodes/` tracers.

## Acceptance

Positive tracers (no trust), under `atomic/by_definition/`:

- `ambient_prop_expand.lit` — user `prop` fork
- `builtin_subset.lit` / `builtin_superset.lit` — standard-set inclusion
- `builtin_coprime.lit` — literal gcd-one
- `builtin_dvd.lit` — rem-zero + multiple witness
- `builtin_injective.lit` — singleton identity
- `builtin_surjective.lit` / `builtin_bijective.lit` — singleton identity plus
  finite membership exist seed `exist x {1} st {x = 1}`
- `builtin_prime.lit` — documents the unsupported trial-forall boundary;
  ordinary `$prime(5)` uses computation, and explicit `by def $prime(5)`
  is rejected without verified definition obligations
- `builtin_is_choice_function_for.lit` — finite index + constant choice fn
  (closes via FnApplicationUnfold rewrite on the forall body; see
  `search_atomic_except_equality_fact_proof_by_builtin_rewrite.rs`)

`$prime` / `$coprime` closed-integer **computation** (ByBuiltinRule on the
dedicated `PrimeFact` / `CoprimeFact` / `NotPrimeFact` / `NotCoprimeFact`
families, not `NormalAtomicFact`) remains under
`atomic/by_builtin_rule/prime_by_computation.lit`,
`not_prime_by_computation.lit`, `coprime_by_computation.lit`,
`not_coprime_by_computation.lit`.

Unit tests also cover `$proper_*` with trusted obligations and finite list-set
subset definition expansion. `by_def_requires_definition_route` asserts the
explicit ByDefinition evidence and rejects arithmetic/equality/SetBuilder
requests; `by_def_rechecks_known_predicate_obligations` rejects unsupported
known abstract predicates and known computed prime targets with unproved definition obligations.

The explicit statement entry calls this definition dispatcher directly, without
ordinary target search. Definition obligations retain full ordinary verification;
the target itself cannot fall back to known facts, builtin rules, or strategies.
The entry retains its local proof Env in the successful result.
