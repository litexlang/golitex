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
| Statement forms | 52 | 21 at the accepted checkpoint | 31 forms lack a consumer; some require an explicit assumptions/model policy |
| Object constructors | 94 | 21 | 73 constructors have no direct WD construction route |
| Standard number sets | 15 | 7 | 8 additional signed/nonzero number sets |
| Atomic fact variants | 72 | 16 proposition renderers | 56 variants lack a proposition renderer, before their proof routes can be replayed |
| Explicit reserved theorem IDs | 364 | 5 Lean-checked adapters | 359 IDs remain; the four membership IDs work through both `release thm` and `by thm` |
| Automatic equality builtin result branches | 232 | 14 explicitly referenced branches | Audit and implement the remaining branches and their nested certificates |
| Automatic non-equality builtin result branches | 397 | 69 explicitly referenced branches | Audit and implement the remaining branches and their nested certificates |
| Builtin strategy result branches | 138 | 19 explicitly referenced branches | 8 equality strategies and 130 non-equality strategies must be tracked separately from builtin rules |

These columns count different things. The first two count dispatcher entrypoints;
the atomic-fact column counts statement rendering; automatic-rule columns count
static references in compiler code. A reference is not a successful Lean check.
No single percentage combines these denominators.

A fresh static scan on 2026-10-23 confirmed these inventory totals and rule
reference counts. The latest accepted addition is `HaveObjByExistFacts`: global
and local choices from a plain existential, including dependent division WD,
pass Lean. Unique existence and the known-forall existential search route still
reject explicitly. A dispatcher arm alone does not complete every proof route.

Statement counting expands `Stmt`, definition, object introduction, `by`,
release, witness, register, trust, proof-block and command enums to leaf forms;
a fact assertion counts once. Object counting expands the operation families
but counts `StandardSet` once, and does not expand identifier qualification,
interval endpoint combinations, function arity or limit approach metadata.
The 15 standard sets are listed separately. Nested evidence enums inside an
automatic rule are not additional rows in the 232/397 counts.

The existing 21 statement entrypoints are fact assertions; `let`; nonempty
carrier introductions; typed equalities; `have` from existence; both `obtain` forms; formula functions;
bounded function induction; concrete predicates; named theorems; theorem
release; `by cases`, `by contra`, `by induc`, `by def`, `by thm`; both existential
witness forms; nonempty-set witnesses; and `claim`. Each retains its existing scope/domain restrictions.

The existing 21 object entries comprise identifiers, calls, numeric literals,
standard sets; add/subtract/negate/multiply/divide/power/absolute value; square
root; union/power set; finite enumeration/bounded builders/closed ranges;
cartesian products/tuples; and function sets/anonymous functions. A formula
such as `f(g(x))` being supported does not imply support for the distinct
`Composition` object constructor.

The seven rendered number sets are `N`, `Z`, `Q`, `R`, `C`, `R+`, and `N+`.
The recent minimal `have a R+` failure concerns a missing generated semantic
parameter, not the absence of the `R+` representation.

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

The counts below allocate work remaining after the accepted checkpoint, not
estimates of development time. Predicate/proof/inference routes belong to each
phase as well; their work is not exhausted by the object count. An existing
entrypoint can also need broader domains or additional selected-proof branches.

| Phase | Deliverable | Remaining statement / object entries | Remaining explicit BT IDs |
| --- | --- | ---: | ---: |
| P0 | Current small failures repaired; retain the accepted baseline | 0 / 0 | 0 |
| P1 | Common proof statements and logical forms; broaden existing membership consumers where needed | 9 / 0 | 0 (four membership IDs delivered within their documented domains) |
| P2 | Elementary scalar operations and number theory | 0 / 11 | 4 |
| P3 | Set operations, finite collections and finite proof iteration | 3 / 22 | 12 |
| P4 | Function/structure/template interfaces and reusable proof declarations | 11 / 7 | 1 |
| P5 | Elementary transcendental and complex operations | 0 / 25 | 0 |
| P6 | Real analysis, delivered in five subphases | 0 / 8 | 340 |
| P7 | Explicit assumptions and foundation-model boundaries | 8 / 0 | 2 |

The remaining columns sum to 31 statement forms, 73 object constructors and
359 explicit BT IDs. The original P1 allocation was eleven forms and four BT
IDs; nonempty witnesses, `have` from existence and all four membership IDs have passed their
focused Lean checks. Completing these inventories still requires the associated
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
