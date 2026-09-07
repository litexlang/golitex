# Litex semantics in Lean

This directory is the new design repository for the Litex-to-Lean semantic
boundary. It is intentionally independent from the old `lean/` tree. The
prototype in [`Core.lean`](Core.lean) is a checked Lean contract; it does not
silently change the production compiler. [`Tracer.lean`](Tracer.lean) is the
first executable rule replay.

The guiding equation is:

```text
Litex object = a typed Lean representative + Litex semantic evidence
Litex identity = Same
Litex membership = In
Lean Eq = a host-language fact that can be injected into Same
```

There is no public `LitexObject` containing every value. A number, function,
tuple, matrix, structure, and set expression keep their own Lean carriers.
The conceptual quotient of all `(carrier, value)` pairs is useful for
understanding Litex, but this implementation keeps representatives and proof
evidence explicit so that Lean's kernel checks the generated term.

## Design decisions the agent must preserve

1. `Same` is heterogeneous semantic equality. It may relate `x : α` and
   `y : β` when a reviewed Litex bridge says that they denote one value. It is
   not `Eq`, `HEq`, or a coercion tactic.
2. `Same.ofEq` is the one-way inclusion `Eq ⊆ Same`. There is no global
   `Same → Eq`; native equality is recovered only by a proved, faithful
   carrier adapter such as a complex-native adapter.
3. `In x S` is membership-oriented. It means that `x` has a `Same` witness in
   the exact carrier selected for `S`. It never changes, casts, narrows, or
   retypes the Lean term `x`.
4. `IsSet A` is source-level sethood. It is not the proposition `A : SetExpr`
   and it is not `A $in Litex.Set`. `isSet_iff` retains a `Same`-certified set
   view for a value whose host type is something else.
5. Set equality is the extension principle: equal `In` observations imply
   `Same` between set expressions. This is the only set identity boundary;
   exact carriers remain implementation data.
6. `Gt`, `Lt`, `Le`, arithmetic, function application, matrix operations, and
   intervals remain Litex predicates and operations in generated theorem
   statements. Their native Lean forms occur only in named bridge theorems or
   in the proof body of a registered rule.
7. The bridge registry is closed at the project boundary. A downstream
   module must not install `relation := fun _ _ => True` and thereby enlarge
   `Same`. An extension is a reviewed rule with a proof certificate and a
   stable rule identifier.
8. Safe Core and ordinary generated modules contain no project `axiom`,
   `sorry`, `admit`, or unsafe proof. An explicit source `trust` belongs to a
   separately marked trusted artifact and is rejected by safe publication.

## What `Core.lean` contains

`Core.lean` defines an explicit `World` contract. A concrete backend will
construct one `World` by proving the fields; the fields are not axioms.
Keeping the contract in one record makes the ownership visible and prevents a
second, target-specific semantic IR from growing inside the emitter.

| Declaration | Meaning and reason it exists |
| --- | --- |
| `World.SetExpr` | Type of Litex set expressions only; it is not a universal object type. |
| `World.carrier` | Exact native Lean carrier selected for one set expression. |
| `World.Same` | The heterogeneous Litex identity relation. |
| `World.In` | Litex membership, independent of host typing. |
| `World.IsSet` | Source sethood for any host value. |
| `World.Gt` | Litex greater-than relation; its public type does not expose `ℝ`. |
| `World.same_of_eq` | Injects homogeneous Lean equality into Litex identity. |
| `same_refl`, `same_symm`, `same_trans` | The equivalence closure required by every proof route. |
| `World.in_iff` | The one named elimination path from `In` to an exact-carrier representative. |
| `World.isSet_iff` | The retained set-view contract for `IsSet`. |
| `World.same_of_set_ext` | Set extension axiom as a checked Litex rule. |
| `World.same_add_real` | Reviewed arithmetic/complex congruence used by the tracer. |
| `World.add_mem_R` | Verifier-owned well-definedness that the sum remains in `R`. |
| `World.gt_zero_to_real` | Adapter-only elimination of a Litex `Gt a zero` fact. |
| `World.gt_zero_of_real` | Adapter-only introduction of the same Litex `Gt` fact. |
| `FactId` | Stable identity for a stored fact; citations never use printed proposition text. |
| `FactShape` and `FactResult` | Typed fact publication shape and its proof. |
| `StmtEffect` | Declaration, scope, and fact-publication effects returned by statement execution. |
| `API.SetView`, `setRep` | Explicit set-view evidence for `forall A set`, `have A set`, and set-valued objects. |
| `API.ComplexView` | Thin observation interface for `N/Z/Q/R/C` and later native structures. |
| `API.same_observation_eq` | Uses an explicitly supplied coherence proof; it does not widen `Same`. |
| `API.Gt.*` | The only public bridge where the real ordered backend is exposed. |

The prototype uses universe-zero host `Type` to keep the contract readable and
kernel-checkable. The production implementation should lift the same fields to
universe parameters as one ABI change; it must not change the semantic roles.

## The two foundations and the standard concepts

`Same` and `In` are the roots. Every other Litex concept is built on them and
stays in Litex form until a consumer deliberately crosses a bridge.

```text
Same
├── Eq injection, reviewed numeric/complex laws, equivalence closure
├── In x S                       (a Same witness in an exact carrier)
├── IsSet A + set extension     (set identity by In observations)
├── Gt/Lt/Le                    (Litex order; native order only in bridges)
├── arithmetic and application  (Same-congruence and WD certificates)
└── function/tuple/matrix facts (extensional or coordinate rules)
```

The first native sets use Mathlib carriers:

```text
N ↦ ℕ       Z ↦ ℤ       Q ↦ ℚ       R ↦ ℝ       C ↦ ℂ
```

The current adapter-facing compiler convention may still lower an `R` or `C`
source binder to a Lean `ℂ` term plus an `In` fact. Membership does not turn
that term into an `ℝ`. A rule obtains an `ℝ` representative only through its
checked bridge.

`ComplexView` gives the common Mathlib boundary:

```text
ℕ → ℂ,  ℤ → ℂ,  ℚ → ℂ,  ℝ → ℂ,  ℂ → ℂ
```

The forward observation `Same → equal observations` is safe when a registered
view supplies its coherence proof. The reverse direction is available only
for a faithful view. Thus an adapter may turn `Same x y` into `x = y` for
`x y : ℂ` or `x y : ℝ`, but generated Litex theorems never assume a global
reverse conversion.

## Placement of every Litex object family

`Obj` is a source classification, not a Lean type tag. Lowering is always:

```text
Obj → semantic family → verifier-selected carrier → Lean term + evidence
```

| Rust `Obj` family | Lean/Core home |
| --- | --- |
| atom, identifier, bound symbol | local declaration keyed by `SymbolId` |
| number, `i`, `e`, `pi` | native `ℕ/ℤ/ℚ/ℝ/ℂ` term and reviewed Complex bridge |
| add/sub/mul/div/pow/mod/quot | typed native operation plus `Same` congruence and WD evidence |
| abs, sqrt, exp, log, trig, min/max | named Litex operation; carrier/domain bridge selected by verifier |
| standard set `N/Z/Q/R/C` | `SetExpr` plus exact `carrier` |
| set builder, union, intersection, difference, power set | subtype or dependent carrier; membership rules use `In` |
| Cartesian product, tuple, projection | typed `Prod`/sigma/HCons spine and coordinate evidence |
| anonymous function, function set, range, replacement | typed function carrier or function graph with membership evidence |
| sequence and finite sequence | telescope/function carrier with explicit index-domain proofs |
| interval, ray, closed range | exact subtype carrier with bound proofs |
| sum, product, reduce, finite-set aggregate | `Finset`/fold target term plus aggregate certificate |
| matrix and matrix operators | dimension-indexed function/carrier plus dimension evidence |
| structure/template/instance/field access | generated Lean declaration, constructor, projection, or definition application |
| big union/intersection/general Cartesian family | dependent family wrapper; unsupported shapes fail closed |

An `Add` therefore does not hard-code `ℂ`: its selected carrier can be
`ℕ`, `ℤ`, `ℚ`, `ℝ`, or `ℂ`, and the Result certificate records that choice.

## Placement of every Fact family

| Litex fact | Lean-facing proposition |
| --- | --- |
| equality / inequality | `Same`, `¬ Same`, `Gt`, `Lt`, `Le`, or their negations |
| membership / sethood | `In x S`, `¬ In x S`, `IsSet S`, `¬ IsSet S` |
| nonempty / finite | predicates over the exact `carrier S` |
| subset / superset | `∀ x, In x A → In x B` and its converse |
| predicate fact | registered predicate application, not a target-side search |
| conjunction / chain | source-order `∧` tree |
| disjunction | source-order `∨` tree |
| existential / unique existential | `∃` / `∃!` with witness Results |
| forall | Lean binders plus retained domain and WD facts; a `set` binder keeps `IsSet` |
| forall-iff | `∀ ..., P ↔ Q` with both direction certificates |
| function equality | a derived function-graph/set-extensional fact; native `funext` is adapter-only |

Every persistent fact has a `FactId`, proposition, proof evidence, owning
scope, visibility, and WD dependencies. A later theorem cites the exact
`FactId`; it does not call `assumption`, search by proposition string, or ask
Lean to rediscover the verifier route.

## Placement of every Stmt family

Statement compilation consumes the recursive Rust `StmtResult` and produces
an environment delta. It is not merely proposition rendering.

| Litex statement | Lean effect |
| --- | --- |
| `let` / `have` object | local `let`/`def` plus retained object evidence |
| `have A set` | `IsSet A` and an exact set view when construction is checked; bare fresh-set construction fails closed |
| function/tuple/cartesian/sequence/matrix definitions | typed declaration and application contract |
| predicate/algorithm/template/structure definition | Lean `def`, `structure`, namespace, or parameterized definition |
| theorem / claim / example | theorem declaration or local proof scope |
| witness / obtain | `Exists.intro`, choice from a retained nonempty fact, and projected facts |
| proof block / sketch / try | lexical scope push/pop and publication policy |
| `by` cases/contra/induction/extension | replay of the exact verifier-selected child Results |
| builtin theorem application | registered `RuleId` certificate → one reviewed Lean theorem/adapter |
| explicit source axiom/trust | trusted artifact only; never inferred by the compiler |
| command/eval | compile-time action or controlled output, not a mathematical theorem |

The effect ledger keeps source order, `SymbolId`, `FactId`, local versus
persistent scope, declarations, witness ownership, and WD trees. The emitter
must not reconstruct these by diffing environments or reparsing printed text.

## Verifier rule contract

The Rust pipeline remains the source of proof truth:

```text
Litex source
  → runtime verification
  → recursive `StmtResult`
  → typed `BuiltinRuleEvidence`
  → Core/Rules theorem adapter
  → generated Lean
  → handwritten Mathlib adapter
```

Each supported rule needs a stable `RuleId`, semantic fingerprint, source and
target shapes, ordered child Result roles, exact `FactId` citations, WD
dependencies, and scope ownership. The Lean side validates this certificate
then calls the named theorem. It does not use `simp`, `aesop`, `linarith`,
`positivity`, or theorem search to discover a different route. A tactic may be
used inside a reviewed theorem implementation when its inputs and output are
already fixed by that theorem; the generated proof still cites that theorem.

An unsupported certificate is a compiler error. It never becomes a generated
`sorry`, `admit`, or invented `axiom`.

## Tracer bullet: the positive-addition rule

The selected source rule is:

```text
a $in R, b $in R, a > 0, b > 0  =>  a + b > 0
```

The public generated theorem has exactly the Litex shape:

```lean
W.In a W.R →
W.In b W.R →
W.Gt a W.zero →
W.Gt b W.zero →
W.Gt (W.add a b) W.zero
```

It does not become `RealPos (a + b)` and it does not put `0 < ar` in the
theorem statement. [`Tracer.lean`](Tracer.lean) implements the replay:

1. Use `gt_zero_to_real` on the two retained `Gt` facts. This is the only
   temporary unwrap and yields representatives `ar`, `br : ℝ` together with
   `Same a (ar : ℂ)` and `Same b (br : ℂ)`.
2. Apply Mathlib's ordinary theorem `add_pos harPos hbrPos`.
3. Use `same_add_real` to identify the Litex sum with the native representative
   `((ar + br : ℝ) : ℂ)`.
4. Use `add_mem_R` for the verifier's output well-definedness and
   `gt_zero_of_real` to wrap the native result back into `W.Gt`.

This is the intended meaning of “a Litex builtin is an axiom in source use but
not a Lean axiom”: Litex registers a convenient theorem name, while the Lean
implementation is a fixed wrapper → Mathlib theorem → wrapper proof.

## Mathlib-style adapter boundary

Generated files may expose stable, source-named theorem declarations in a
generated namespace. They should not expose `__fact17` as a user API. A thin
handwritten adapter may then:

```text
native Lean parameters
  → In/Same bridge hypotheses
  → generated Litex theorem
  → faithful Same-to-Eq or Complex observation theorem
  → ordinary Mathlib statement
```

The adapter can turn `Same` into native equality only after identifying one
faithful common carrier. It can turn `In x C` into a complex representative
only through the exact `carrier C`. It can use `funext` for same-typed native
functions after proving pointwise `Same`; function equality itself remains a
set-extensional Litex fact. The adapter does not redo induction, proof search,
or the source theorem.

## Implementation order

1. Freeze this `World` contract and close the bridge registry.
2. Add the universe-polymorphic production implementation of `Same`, exact
   carriers, `In`, `IsSet`, and set-view coherence.
3. Make Rust `Obj`, `Fact`, `StmtResult`, WD trees, and builtin evidence emit
   the fields above with stable identities and source order.
4. Add exhaustive lowering by semantic family; unsupported variants fail closed.
5. Register builtin rules by `RuleId` and validate certificates before theorem
   emission.
6. Build the generated theorem → thin adapter → final Mathlib showcase around
   the tracer in `Tracer.lean`.
7. Only then widen to tuples, functions, aggregates, intervals, matrices,
   structures, and templates using the same contracts.

The prototype is intentionally honest about its boundary: `World` is the
semantic ABI contract, while a production `World` constructor and the Rust
compiler migration are later work. This keeps the design inspectable without
pretending that a design file has already translated every source variant.

## Checks

From the existing repository's Lean environment, the two files are checked by:

```sh
cd ../lean
lake env lean -R .. ../litex_semantics_in_lean/Core.lean
lake env lean -R .. ../litex_semantics_in_lean/Core.lean \
  -o ../litex_semantics_in_lean/Core.olean
LEAN_PATH="../litex_semantics_in_lean:$LEAN_PATH" \
  lake env lean -R .. ../litex_semantics_in_lean/Tracer.lean
```

The `.olean` command is only a local import check for `Tracer.lean`; generated
binary artifacts are not part of this design repository. The acceptance
boundary is that both source files type-check, contain no project axiom or
proof hole, preserve the Litex-facing tracer statement, and leave production
`lean/` and Rust files unchanged.
