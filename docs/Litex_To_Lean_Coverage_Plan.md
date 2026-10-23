# Litex-to-Lean coverage plan

Working-tree inventory: 2026-10-23. This is an implementation plan, not an
announcement of additional compiler support. Geo is outside this plan's
acceptance targets.

The current compiler already checks a useful combination of elementary
algebra, inequalities, sets, formula functions and named proofs. The next goal
is to expand this combination across the language by following its existing
statement, WD, verification and inference results.

## Current inventory

| Layer | Inventory | Existing compiler entrypoints | Remaining work |
| --- | ---: | ---: | --- |
| Statement forms | 52 | 19 | 33 forms have no successful dispatcher route; some require an explicit assumptions/model policy |
| Object constructors | 94 | 21 | 73 constructors have no direct WD construction route |
| Standard number sets | 15 | 7 | 8 additional signed/nonzero number sets |
| Atomic fact variants | 72 | 16 proposition renderers | 56 variants lack a proposition renderer, before their proof routes can be replayed |
| Explicit reserved theorem IDs | 364 | 1 through `release thm` | 363 IDs have no explicit theorem adapter; `by thm` currently accepts user theorems only |
| Automatic equality builtin result branches | 232 | 14 explicitly referenced branches | Audit and implement the remaining branches and their nested certificates |
| Automatic non-equality builtin result branches | 397 | 69 explicitly referenced branches | Audit and implement the remaining branches and their nested certificates |
| Builtin strategy result branches | 138 | 19 explicitly referenced branches | 8 equality strategies and 130 non-equality strategies must be tracked separately from builtin rules |

These columns count different things. The first two count dispatcher entrypoints;
the atomic-fact column counts statement rendering; automatic-rule columns count
static references in compiler code. A reference is not a successful Lean check.
No single percentage combines these denominators.

Statement counting expands `Stmt`, definition, object introduction, `by`,
release, witness, register, trust, proof-block and command enums to leaf forms;
a fact assertion counts once. Object counting expands the operation families
but counts `StandardSet` once, and does not expand identifier qualification,
interval endpoint combinations, function arity or limit approach metadata.
The 15 standard sets are listed separately. Nested evidence enums inside an
automatic rule are not additional rows in the 232/397 counts.

The existing 19 statement entrypoints are fact assertions; `let`; nonempty
carrier introductions; typed equalities; both `obtain` forms; formula functions;
bounded function induction; concrete predicates; named theorems; theorem
release; `by cases`, `by contra`, `by induc`, `by def`, `by thm`; both existential
witness forms; and `claim`. Each retains its existing scope/domain restrictions.

The existing 21 object entries comprise identifiers, calls, numeric literals,
standard sets; add/subtract/negate/multiply/divide/power/absolute value; square
root; union/power set; finite enumeration/bounded builders/closed ranges;
cartesian products/tuples; and function sets/anonymous functions. A formula
such as `f(g(x))` being supported does not imply support for the distinct
`Composition` object constructor.

The seven rendered number sets are `N`, `Z`, `Q`, `R`, `C`, `R+`, and `N+`.
The recent minimal `have a R+` failure concerns a missing generated semantic
parameter, not the absence of the `R+` representation.

The sole explicit reserved-theorem adapter is
`tuple_equal_from_coordinates`, through theorem release and within its finite
coordinate boundary. This count does not include automatic arithmetic rules.
The existing compiler can therefore replay an automatic membership proof while
rejecting a mathematically similar explicit `release thm set_builder_member(...)`.

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

A first elementary batch contains 21 currently unreferenced equality branches:

- Square roots: `SqrtZero`, `SqrtOne`, `SqrtOfSquare`, `SqrtProduct`,
  `SqrtQuotient`, `SqrtOfSquareEqualsAbs`.
- Absolute values: `AbsOfNegation`, `AbsProduct`, `AbsSquare`,
  `AbsAbsAbsorption`, `AbsNonposEqualsNegation`.
- Powers: `NegativeIntegerPowerReciprocal`, `PowerOfProduct`,
  `ReciprocalAsNegOnePower`, `QuotientAsMulNegOnePower`, `OneToAnyPower`,
  `ZeroToPosNatPower`.
- Min/max: `MinIdempotent`, `MaxIdempotent`, `MinCommutative`, `MaxCommutative`.

These names come from the current result enum. Their full adapter signatures
and nearest rejected domains remain implementation work.

## Phases

The counts below allocate missing entrypoints, not completed features or
estimates of development time. Predicate/proof/inference routes belong to each
phase as well; their work is not exhausted by the object count.

| Phase | Deliverable | Additional statement / object entries | Additional explicit BT IDs |
| --- | --- | ---: | ---: |
| P0 | Repair current small failures and preserve the accepted baseline | 0 / 0 | 0 |
| P1 | Common proof statements, logical forms and the explicit BT entrypoint | 11 / 0 | 4 |
| P2 | Elementary scalar operations and number theory | 0 / 11 | 4 |
| P3 | Set operations, finite collections and finite proof iteration | 3 / 22 | 12 |
| P4 | Function/structure/template interfaces and reusable proof declarations | 11 / 7 | 1 |
| P5 | Elementary transcendental and complex operations | 0 / 25 | 0 |
| P6 | Real analysis, delivered in five subphases | 0 / 8 | 340 |
| P7 | Explicit assumptions and foundation-model boundaries | 8 / 0 | 2 |

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

P2 adds min/max, floor/ceiling/sign, mod/quotient/gcd/lcm/factorial and the
imaginary-unit literal. Extend the remaining eight signed/nonzero number sets.
Start automatic equality work with the 21-rule batch above, then cover the
associated WD, closure, order, primality/divisibility and inference branches.
The four named BTs are reduced rational representation, gcd with a prime,
prime divisibility of a product, and prime divisibility of a power.

P3 adds the eight remaining set operators, five remaining set-former families,
six iterated operators and three finite-set statistics. Add finite enumeration,
finite `by for`, range expansion, missing subset/nonmembership/finite predicates
and their inference rules. Sequence carriers may initially reuse the existing
unary function interface; general higher-order use is completed in P4.
The two indexed-cartesian choice theorems are reserved for P7.

P4 completes case-defined and uniquely selected functions, abstract predicates,
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
releases and `sketch`, plus the two indexed-cartesian choice BTs. Arbitrary source
`trust` cannot become an unconditional Lean proof. If assumption-preserving
export is wanted, its output must expose the assumptions. Choice, Zorn,
regularity and replacement need the appropriate represented domains and set
model; `Classical.choice` alone does not establish every set-theoretic contract.
`sketch` must be classified by its actual result and export behavior, not
assumed to introduce an axiom. Foundation/assumption policy remains a maintainer
choice before implementing that mode.

## Acceptance for each increment

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
