# Mathematical Collections

The consolidated example ledger is an executable map of the current
Litex-to-Lean interface rather than a new mathematical theory. Its central
collection is the set of source judgments whose verifier evidence has a
checked native Mathlib interpretation.

## Native numeric carriers

Litex standard-set objects `N`, `Z`, `Q`, `R`, and `C` denote universal sets
over Mathlib's `ℕ`, `ℤ`, `ℚ`, `ℝ`, and `ℂ`. A numeral has no intrinsic source
carrier. Membership, a bounded parameter, or another checked judgment supplies
the target expectation only where needed.

The representative interface is:

```litex
2 $in R

forall z Z:
    z / 2 $in Q
```

The intended Lean shapes are `2 ∈ (Set.univ : Set ℝ)` and
`(z / 2 : ℚ) ∈ (Set.univ : Set ℚ)`. The nearest rejected shape is a
closed ambiguous division admitted only by `trust`; proof provenance must not
select its carrier.

Compact numeric subsets keep the same native carrier and compile to predicate
sets rather than new target types:

```litex
forall r R+:
    r $in R+
```

Here `R+` becomes `{r : ℝ | 0 < r}`. The same checked interface covers
`N+`/`Z+` (positive naturals), `Q+`, `Z-`/`Q-`/`R-`, and
`Z*`/`Q*`/`R*`/`C*`. Membership remains an ordinary proposition in every
case. Litex has no ordered `C+` standard set, so the compiler does not invent
one. Closed numeric facts such as `2 $in R+`, `0 - 1 $in Z-`, and
`not 0 $in C*` are discharged by checked numeric reflection in Lean rather
than by a generated axiom.

Standard numeric membership projections use one explicit builtin certificate,
not target-type inference shortcuts. For example, `forall n N: n $in Z`
retains the source premise `n $in N`, validates `N -> Z` against the centralized
Litex hierarchy, and emits the target occurrence as `(n : ℤ)`. The same rule
covers same-carrier refinement erasure and the supported
`N -> Z -> Q -> R -> C` widening paths. It does not assign an intrinsic type to
`n`. Direct heterogeneous set propositions such as `N $subset Z` remain a
separate, deliberately unsupported semantic choice.

## Facts and proof evidence

Facts remain propositions rather than objects. Bounded universal facts retain
both the native binder carrier and their membership premises. Native equality,
arithmetic, order, and supported set operations are emitted directly. An
explicit Litex `trust` is the only source construct in this repository that may
become a Lean axiom.

The examples cover direct facts, definition reduction, known-forall
instantiation, equality transport, rational normalization, typed builtin
rules, recursive additive evidence, checked choice, existential introduction
and elimination, named-prop definition projection, case splitting, and
contradiction scopes.

The
[`obtain_from_existential_prop_definition`](litex_to_lean_examples.md#obtain_from_existential_prop_definition)
section retains the verified prop fact as the sole premise of a checked
definition-projection node. Its Lean snapshot unfolds that definition with
`simpa only`, then feeds the resulting existential to the ordinary
`Exists.choose` and `choose_spec` elimination path.

The [`mixed_projected_forall`](litex_to_lean_examples.md#mixed_projected_forall)
section records the clause-coverage boundary. Its one source universal becomes
the two universal facts actually stored by the runtime, so the real symbol and
the polymorphic set symbol keep independent native carriers and reusable
FactIds. The nearby rejected form is a heterogeneous equality between those
symbols; separate reflexive conclusions do not authorize carrier unification.

The [`builtin_predicates`](litex_to_lean_examples.md#builtin_predicates)
section fixes the first native builtin-proposition tranche. Closed prime facts
become `Nat.Prime` and use checked `norm_num` reflection. Superset reverses the
arguments of native `⊆`; its duality proof retains the exact subset premise.
Proper subset/superset become containment plus inequality, while their negative
forms use Litex's direct `not containment OR equality` definition. Negated
comparisons remain logical negations of native order relations.

This section intentionally separates proposition coverage from proof-route
coverage. It does not claim compilation of explicit proper-relation `by def`
proof statements, function predicates, or cartesian/tuple predicates.

The [`carrier_boundaries`](litex_to_lean_examples.md#carrier_boundaries)
section keeps source facts that Litex verifies but whose current proof route is
not fully represented by the strict backend. This includes several numeric
membership-closure facts and `have` value checks over `N`, `Z`, `Q`, and `C`.
Their native target carriers are settled; their missing proof backends are
reported rather than replaced.

The strict `object_definitions` example uses a real numeral. A real division
definition is left as a commented boundary because Mathlib requires that
generated declaration to be `noncomputable`; accepting the Litex source alone
is not counted as successful backend coverage.

## Native sets

A general Litex set parameter becomes `Set α` for one implicit element
carrier. `union`, `intersect`, and `set_minus` map to native Mathlib set
operations. This avoids a monomorphic `LitexSet` universe while preserving the
source claim that all Litex objects satisfy `$is_set` through a polymorphic
object marker.

The `native_set_builtins` and `builtin_arithmetic` ledger sections also check
the generic paired-rule path. Rule schemas keep `$is_set(A)`, `x $in A`, and
numeric carrier membership as ordinary proof requirements. Checked adapters
receive native `Set α`/`ℝ` values and those exact proofs. A dependent binder
such as `x A` carries only an occurrence-local view of `A`'s element carrier,
not a global type annotation on Litex objects.

Binder-owning set builders and several richer object families remain outside
this executable collection. They are not approximated by axioms or custom
equality.

## Honest incomplete output

The two partial sections record the distinction between source verification
and backend coverage. In particular, report-mode To-Lean omits the currently
unsupported `sin(0) = 0`, emits both surrounding rational facts, and reports
`Incomplete`. These boundaries are intentional and have no proof, existence,
uniqueness, or hidden-trust workaround.
