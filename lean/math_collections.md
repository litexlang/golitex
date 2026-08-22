# Mathematical Collections

## Scope

This document records the mathematical design of the v2 set system. The source
of truth is the single semantic bridge header `Litex/Core.lean`, the concrete
verifier-rule theorems in `Litex/Rules.lean`, and the same-name generated pairs
under `examples/`. Concept definitions and Lean/Mathlib representation bridges
must not be split into feature headers beside `Core.lean`.

`Litex.lean` is the public umbrella import. Generated files depend on that
stable entrypoint rather than on the current internal module list; future
supported theorem or strategy modules join the umbrella without changing the
compiler's generated header.

The first unary function-set/application interface is included together with
the set system. The first ordered-numeric interface fixes how native Mathlib
order is reached without retyping Litex objects.

## Representation bridge

`Core.lean` owns a closed representation registry. Private proof constructors
connect native naturals, integers, rationals, and reals to their canonical
complex embeddings; the subtype edge connects a member of a predicate-defined
carrier to its base value. Downstream Lean code can use the public `Same`
interface but cannot add another primitive or derived edge.

This primitive relation matters because reflexivity, symmetry, and
transitivity alone cannot create genuine cross-carrier equality.

Immediate use: `Litex.Same.complexReal r` relates `(r : ℂ)` to `r : ℝ`.

Nearest rejected form: silently treating all values of unrelated Lean types as
bridged. There is no public registration API for a `Bool`-to-`Nat` edge;
adding another carrier relation requires changing and reviewing `Core.lean`.

## Semantic equality

`Litex.Same x y` is the public equivalence closure of the closed
representation edges. Native Lean equality implies `Same` through
`Litex.Same.ofEq`; public numeric/subtype theorems expose the reviewed
cross-carrier cases without exposing the registry.

The closed derived layer currently contains native real-to-complex
congruence for `+`, `-`, `*`, and `/`. These are the exact operations used
by the named-function compiler adapter.

Immediate use: a proof of `Same a b` transports `In a S` to `In b S` without
changing either Lean variable's carrier.

Open obligation: later extensional function and predicate interfaces must
state how they respect `Same`. The current unary wrapper is a proof-carrying
call interface; it does not claim function extensionality.

## Real representatives and order

`Litex.AsReal x r` is `Litex.Same x r` with `r : ℝ`. Consequently,
`Litex.In x Litex.R ↔ ∃ r, Litex.AsReal x r` holds definitionally. This keeps
real membership in the same object/set semantics instead of introducing a
second casting subsystem.

`Litex.OrderValue z := z.re` is the canonical Mathlib-ordered observation of
the compiler's numeric `ℂ` carrier. Custom `Litex.Lt x y` and `Litex.Le x y`
apply native real `<` and `≤` to those two canonical observations. Source
admission remains verifier-owned: the generated theorem retains exact `In _ R`
proofs even though the relation itself reduces definitionally to Mathlib.

Zero-ended source comparisons take a canonical route. The compiler lowers
`0 < x` to `Litex.Positive x` and `0 ≤ x` to `Litex.Nonnegative x`. Each
proposition stores one `AsReal` witness for `x`; its zero endpoint is
Mathlib's native real zero rather than another independently selected Litex
representative. Sign rules use this contract.

Example 2 implements the general-order contract. Its verifier certificate
retains the real-carrier conjunction followed by the two ordered premises;
compiler validates the endpoints, one shared middle term, and strictness before
calling `Litex.Lt.trans`, `Lt.transLe`, `Le.transLt`, or `Le.trans`. There is no
`RealCoherence` declaration or assumption. The nearest boundary is executable:
the verifier rejects `forall a, b C: a < b` because both operands must belong
to `R` before compiler IR exists.

## Exact-carrier sets

`Litex.Set` contains one field, `Carrier`. The carrier is the exact extension
of the represented set, not an ambient type paired with `Set.univ`.

For a new hidden mathematical carrier `__Marker`, the set is
`Litex.Set.ofType __Marker`. Every `marker : __Marker` belongs to it by
`Litex.In.own`.

For a predicate-defined subset, `Litex.setBuilder base predicate` uses the
subtype `{x : base.Carrier // predicate x}` as its exact carrier.

The implemented standard refined carriers use that same contract:
`Litex.NPos = Litex.setBuilder Litex.N (fun n => 0 < n)`,
`Litex.RPos = Litex.setBuilder Litex.R (fun r => 0 < r)`, and
`Litex.ZStar` / `QStar` / `RStar` / `CStar` use `Litex.C` as the exact source
carrier with predicate `In x base ∧ ¬ Same x 0`. Each star carrier therefore
retains the source-level base membership and semantic nonzero certificate;
none is an alias of its base set.

The construction remains universe-polymorphic. In particular,
`Litex.Set.{0} : Type 1`, so it may be the carrier of `Litex.Set.{1}`. A
generated example is deferred until compiler supports the corresponding
Litex statement form; the examples ledger contains no hand-written substitute.

Nearest rejected form: using the same carrier for a base set and a proper
subset. That would collapse their memberships.

## Heterogeneous membership

`Litex.In x S` means that some `y : S.Carrier` satisfies `Litex.Same x y`.
It is an ordinary proposition and never changes the Lean type of `x`.

The central use probe first defines the checked aliases `A = R` and `B = C`,
then starts with `a b : ℂ`, `a In A`, `b In B`, and `Same a b`, deriving
`b In A` and `a In B`. Its authoritative source is
`examples/1_SetSystem.lit`; the aliases become `Litex.Set` abbreviations and
verifier equality-rewrite evidence becomes `Litex.In.congr` in the paired
generated Lean file. A bare `have A set` is intentionally not synthesized by
the emitter: the verifier currently rejects that arbitrary choice because no
checked inhabited-type backend exists for the meta-level parameter type
`set`.

## Standard numeric membership hierarchy

The base standard sets have exact native carriers `ℕ`, `ℤ`, `ℚ`, `ℝ`, and
`ℂ`. Membership widening does not coerce or replace the source Lean value.
Instead, `Rules.inZOfInN`, `inQOfInZ`, `inROfInQ`, and `inCOfInR` unpack an
existing witness, embed that witness into the next native carrier, and rebuild
`Litex.In` through the closed numeric `Same` bridges. The compiler validates
the verifier's exact `StandardSetMembershipProjection` source and target, then
composes only these adjacent rules.

Example 16 covers every proper pair in `N → Z → Q → R → C`. This matters
because a single complex-valued source binder can keep several independently
proved memberships without native Lean typing becoming the source set
semantics.

Example 20 adds the exact `N+ → N` edge. The source remains a complex-valued
object with `Litex.In n Litex.NPos`; `Rules.inNOfInNPos` projects the selected
subtype witness to its native-natural base without reconstructing or erasing
the witness's positivity proof.

Example 21 adds `R+ → R` and composes it with `R → C`. Like the `N+`
projection, it forgets only the exact subtype predicate while retaining the
selected native witness.

Example 22 adds predicate-preserving nonzero widening
`Z* → Q* → R* → C*` and predicate-forgetting projections from each star set
to its base carrier. Base hierarchy bridges then reach every supported base
supercarrier. Each star-to-star rule keeps the same complex representative and
semantic nonzero proof while widening only the retained base membership.

Nearest rejected form: `Q+ → Q`. `Q+` still needs its own exact predicate
carrier and proved projection rather than a rename of either implemented set.

## Positive-natural reflection

Example 20 also gives closed positive-natural numerals their exact constructor.
After verifier evidence identifies `1 $in N+`, compiler independently requires
a nonzero natural numeral and calls `Rules.complexEqNatInNPos`. The theorem uses
the closed complex-to-natural `Same` bridge and `Rules.inSetBuilder`; it does
not turn native positivity into the heterogeneous `Litex.Lt` relation or
assume `RealCoherence`.

Nearest rejected form: `1 $in Q+`. The positive-rational carrier remains
unimplemented even though the closed source fact verifies.

## Positive-real carrier and elimination

Example 21 defines `RPos` as the subtype `{r : ℝ // 0 < r}`. Closed positive
numerals use an explicit complex-to-real equality bridge; `e` and `pi` use
Mathlib's `Real.exp_pos` and `Real.pi_pos`. Membership projects to `R` and then
to `C` without retyping the source object.

`Rules.positiveOfInRPos` opens the exact subtype witness and constructs
`Litex.Positive x` with that same real representative. The forall emitter
materializes this verifier-inferred rule under its retained FactId before a
later conclusion cites it.

Nearest rejected form: constructing `x $in R+` from separate `x $in R` and
`x > 0` premises. The two wrapper propositions may select different real
representatives, so the active compiler rejects the verifier's generic refined
membership certificate instead of silently assuming `RealCoherence`.

## Nonzero numeric carriers

Example 22 gives `Z*`, `Q*`, `R*`, and `C*` exact certified complex-source
subtype carriers. The four constructor rules consume the verifier's ordered
premises `x $in base` and `x != 0`, select a complex representative already
proved `Same` to `x`, and retain both the transported base membership and
semantic nonzero proof in the subtype predicate.

Membership projects back to `Z`, `Q`, `R`, or `C` by opening that same
certificate. Predicate-preserving widening along `Z* → Q* → R* → C*` keeps
the representative and nonzero proof unchanged and widens only its base
membership through the reviewed hierarchy rules.

The inverse inference is constructive without a global endpoint theorem. From
`x $in Z*`, for example, the exact subtype supplies a complex representative
`z`, `Same x z`, and `¬ Same z 0`. An assumed `Same x 0`, combined with
symmetry and transitivity, contradicts the retained certificate. The same
argument applies to `Q*`, `R*`, and `C*` and materializes the exact
verifier-inferred nonzero FactId.

Nearest rejected form: closed reflection such as `1 $in Z*`. Litex verifies
the source, but its retained `1 != 0` child still needs a separately reviewed
closed negated-equality emitter. Example 22 does not generalize closed
non-equality into target-side proof search, and star arithmetic closure remains
a later evidence-adapter batch.

## Native mathematical constants

Example 19 gives the three primitive source constants ordinary Mathlib terms:
`i` is `Complex.I`, `e` is the complex embedding of `Real.exp 1`, and `pi` is
the complex embedding of `Real.pi`. They therefore participate in `Same` and
native complex expressions without a universal object wrapper.

`NativeConstantMembership` proves `i $in C`, `e $in R`, and `pi $in R` through
fixed theorem adapters after validating both the constant and the target set.
The verifier represents `e $in C` and `pi $in C` as the corresponding real
membership followed by `StandardSetMembershipProjection`, so compiler reuses
the exact real-membership FactId and the proved `inCOfInR` bridge.

Example 21 constructs `e $in R+` and `pi $in R+` through fixed native-constant
adapters. The nearest rejected constant-adjacent refined form is `1 $in Q+`;
positive-rational membership cannot reuse the real subtype.

## Unary function sets and application

`Litex.Fn s S` contains one call field
`{α : Type u} → (x : α) → Litex.In x s → S.Carrier`, where `s : Set u`
and `S : Set v` may use different universes. Consequently
`fnSet s S : Set (max (u + 1) v)`. A value is
therefore not callable merely because of its Lean carrier: the call still
needs the Litex proof that its argument belongs to `s`.

`Litex.fnSet s S` packages `Fn s S` as an exact-carrier `Litex.Set`.
`Litex.fnApply f hf x hx` first selects the `Fn s S` representative supplied
by `hf : Litex.In f (Litex.fnSet s S)`, then calls it with
`hx : Litex.In x s`. Both proofs are explicit inputs. The result is directly
an `S.Carrier`; this wrapper layer has no inverse transport API.

`Litex.fnApplyOwn` is the companion path for a compiler-constructed value
whose Lean type is already exactly `Fn s S`. It still takes the stored
`f $in fn(...)` proof and the argument-membership proof, but it does not make a
second representative choice for `f`. Example 12 uses this path for
`have fn id(x R) R = x`; its result is the representative already carried by
`x $in R`, and `Same.symm (In.same_rep x hx)` proves the checked defining
reduction.

`Litex.FnWhere s S requires` adds one explicit proposition after argument
membership. `fnSetWhere`, `fnApplyWhere`, and `fnApplyWhereOwn` preserve
that exact contract. Example 12 uses it for
`reciprocal(x R: x != 0) = 1 / x`: the application must pass the verifier's
nonzero WD FactId even though Mathlib division itself is total.

The first authoritative probe is `examples/4_FunctionSet.lit`. Its generated theorem
quantifies independent carriers for `x` and `f`, retains both membership
hypotheses, and emits both occurrences of `f(x)` with the exact
verifier-selected FactId/WD proofs. The nearest negative probe lives under
the compiler's function-set regression: changing `x s` to `x S` is rejected
by Litex before Lean emission.

The multi-layer probe is `examples/23_MultilayerApplication.lit`. For
`g(a)(b)`, the verifier WD DAG contains a proper-prefix object for `g(a)` with
`intrinsic_result_set = fn(y T) U`, followed by a final object whose direct
argument requirement is `b $in T`. Generated Lean binds the first result once
with `let __fn_layer1 := fnApply g ...`; because that value already has the
exact `Fn T U` carrier, the second call uses `fnApplyOwn __fn_layer1` together
with the explicit `In.own (fnSet T U) __fn_layer1` certificate. Longer unary
chains repeat this prefix recipe rather than flattening layers.

One source layer with several parameters uses `Litex.FnTelescope`. A
`parameter` node retains each exact set and supplies the argument plus its
`In` proof to the rest of the signature. A `requirement` node retains the
ordered conjunction of source domain clauses after the arguments they may
mention. The `done` node stores the exact codomain. Its carrier is a dependent
function ending in `ULift codomain.Carrier`, so the recursive signature stays
universe-correct without erasing the result carrier.

`fnTelescopeSet`, `fnTelescopeApply`, and `fnTelescopeApplyOwn` are the
same-layer counterparts of the unary ABI. Example 23 checks both quantified
and named `f(a,b)`. A named telescope function is referenced as the whole
value `@f`; otherwise Lean would eagerly synthesize its first implicit
heterogeneous carrier and partially apply it. The negative boundary remains
`f(a)(b)`: neither the compiler nor Lean currying may repair that different
source syntax.

Named real functions support identity and expression trees built from their
parameters, natural literals, and `+`, `-`, `*`, `/`. Checked reduction uses
the closed native-operation `Same` congruence theorems. Application of an
already quantified function may also cross arbitrarily many independent unary
source layers.

Example 24 makes the telescope genuinely dependent. `fn(x R, y {z R: z > x})
R` renders the second exact carrier only after receiving `x` and its retained
`R` membership, while `fn(x R) {z R: z > x}` returns that argument-indexed
subtype directly. The compiler uses the canonical numeric view only inside
the dependent carrier; zero-ended `Positive` and `Nonnegative` domain clauses
remain propositions on the original heterogeneous argument.

The same example constructs compound anonymous `R -> R` values. Each literal
is tied to its exact parser occurrence and verifier-owned binder scope. Its
parameter premise is named locally, its typed body-membership closure is
replayed, and the native real expression is returned. Direct application must
also identify the exact `FunctionHead` WD child. Other construction
domains/codomains and operators outside the reviewed real-expression family
remain rejected.

## Explicit source axiom boundary

`Core.lean` and `Rules.lean` contain no axioms. Example 25 handles the two
source forms which explicitly request opacity or trust. An `abstract_prop`
with arity `n` becomes one source-scoped Lean predicate axiom with `n`
independently universe-polymorphic object arguments. It supplies an interface,
not a proof of any application. An explicit `trust` proposition becomes one
separate source-scoped axiom under its exact stored FactId. Later citations and
all verifier-inferred consequences are ordinary theorems.

The focused compiler audit counts exactly those declarations and verifies that
an ordinary checked source creates none. Litex `-strict` continues to reject
explicit user trust by design; this tracer is gated by the ordinary release
runner, exact generated-axiom audit, and the real Lean kernel.

## Concrete predicates

A concrete source `prop P(x S): ...` becomes a native Lean predicate whose
body conjoins `Litex.In x S` with the rendered defining clauses. This makes
parameter admission part of the wrapper proposition instead of letting Lean
argument typing stand in for Litex membership. Example 13 replays the exact
membership and clause proofs for `by def` and projects inferred components by
their position in that same conjunction.

Nearest rejected form: `abstract_prop` or a bodyless concrete predicate. No
checked Lean definition exists for either, so compiler does not manufacture
an axiom or arbitrary proposition.

## Set-builder membership and choice

Example 14 gives the existing `setBuilder` subtype carrier its first generated
construction route. A checked literal membership supplies base membership and
the defining facts in source order. The adapter transports whole-side
equalities such as `x = 1` to the selected base representative. A
one-parameter concrete predicate is unfolded into its membership requirement
and equality clauses; the inverse inference from set-builder membership uses
the explicit `SetBuilderPredicateProjection` IR rule. The inferred
`x $in base` fact remains the proved `Rules.inBaseOfInSetBuilder` projection.

Nearest rejected form: a changing binder nested inside an expression, such as
`x + 1 = 2`. The current adapter does not recursively prove predicate
respectfulness for arbitrary object constructors.

`Litex.Set.Nonempty S` is native `Nonempty S.Carrier`. A source `have x S`
therefore chooses an ordinary value of the exact carrier and proves its
membership with `In.own`. The verifier must supply the nonemptiness proof; a
bare meta-level `have A set` remains rejected.

## Existential witnesses

A supported positive existential has one witness and one body fact. Over a
standard numeric set it is rendered as `∃ x : ℂ, Litex.In x S ∧ body`. Over
an arbitrary Litex set it instead quantifies a Lean carrier and a value in that
carrier, then states the same explicit membership proposition. Thus the Lean
type chosen for the witness is representation data; `Litex.In x S` remains
the semantic admission condition.

Introduction consumes the verifier's exact parameter-membership and body
proofs. Elimination cites the stored existential FactId, selects its native
witness with Lean's ordinary classical choice, and emits separate theorems for
the retained parameter and body projection roles. Nothing is transported back
from the wrapper because the witness already is an ordinary Lean value.

The authoritative pair is `examples/10_ExistentialWitness.lit/.lean`. The
negative Rust tracer keeps multiple witnesses outside this reviewed slice.

## Proof scopes and object definitions

Named theorems, claims, examples, cases, and contradictions preserve their
source-local environments by cloning the compiler render context. FactId joins
are installed only in the scope in which the verifier produced them. These
routes are traced by examples 8 and 9.

Minimal object definitions create native Lean definitions rather than a
universal Litex carrier. The defining relation is still `Litex.Same`; a typed
`have x S = value` additionally replays the checked `Litex.In x S` fact.
Example 11 fixes this contract for closed numeric values.

## Builtin strategy replay

Example 15 retains `UseBuiltinStrategy` as provenance around the exact
recursive rule tree; compiler never reruns the strategy in Lean. Complex-
carrier values with separately proved real membership use
`Rules.complexAddInR`, `complexSubInR`, `complexMulInR`, and `complexDivInR`
for the four basic real carrier closures. The three reviewed additive sign
adapters cover nonnegative plus nonnegative and either one of the two ordered
summands being strictly positive. Both a direct arithmetic certificate and a
registered local-rule certificate validate their ordered operands before
calling the corresponding theorem.

Example 15 also covers `AddPositive`, `MulNonnegative`, `MulPositive`,
`DivNonnegative`, and `DivPositive`, including recursive strategy children
whose registered rule IDs and semantic fingerprints are validated exactly.
The adapters open one representative per operand and call Mathlib's native
sign theorems. No generated theorem receives a `RealCoherence` parameter and
no project axiom is added.

Nearest rejected form: `a ≤ b → 0 ≤ b - a`. The verifier retains
`SubNonnegativeFromLessEqual`, but that separate adapter family remains
fail-closed and has an executable negative compiler regression.

## Base numeric arithmetic closure

Example 17 separates result-carrier closure from order reasoning. For a
complex-valued source expression, the `C` carrier is exact: the result of
native complex `+`, `-`, `*`, or `/` belongs to `C` by `In.own`. The verifier
selects a zero-child `ComplexArithmeticMembershipClosure` certificate because
operand admission and division well-definedness are already retained in the
owning statement's WD graph. Compiler validates the exact target operator and
set before calling the corresponding `Rules.complex*InC` theorem.

Integer closure is constructive rather than a type cast. From
`Litex.In a Z` and `Litex.In b Z`, the proved adapters select witnesses
`za zb : ℤ`, relate the complex source values to the corresponding real
embeddings, apply the closed real/complex operation congruence, and rebuild an
integer witness for `za + zb`, `za - zb`, or `za * zb`. Emitter requires the
exact ordered binary conjunction carried by `IntegerMembershipClosure`.

Nearest rejected form: `a % b $in Z`. Litex verifies it and IR records `Mod`,
but source numeric values currently lower to `ℂ`, where there is no native
remainder operation matching the source meaning. Adding a symbolic wrapper or
retyping operands would be a new object ABI decision, so compiler rejects it.

Example 18 extends the same constructive pattern to exact rational and natural
carriers. Rational `+`, `-`, `*`, and `/` select `ℚ` witnesses, use the closed
real/complex operation bridges, and reconstruct a `ℚ` result witness. Natural
`+` and `*` do the same with `ℕ`; natural subtraction is deliberately not
inferred from this closure family. The verifier records
`RationalMembershipClosure` and `NaturalMembershipClosure` with their ordered
operand facts, so Lean source construction validates the target operator, set, and operands
instead of rediscovering a theorem.

Nearest rejected rational form: `a^z $in Q` for `a $in Q`, `z $in Z`. Its
operator-specific `Pow` certificate reaches the recursive Result, but the complex-valued source
power term and native exponent semantics have not received a reviewed compiler
contract. It therefore remains fail-closed.

## Exact complex algebraic equality

Example 54 consumes `ComplexAlgebraicNormalization` evidence for an exact
source equality. Both source sides are represented by ordinary native complex
terms, including `Complex.I`; the compiler reruns the bounded verifier
normalizer and then lifts the checked native equality through
`Litex.Same.ofEq`. This matters because the backend follows a typed verifier
route instead of recognizing a diagnostic label or launching open-ended Lean
search.

Immediate use: `2 * i + 1 = i * i + 2 + 2 * i`, closed reciprocal identities,
and polynomial identities in a `C` binder.

Nearest rejected form: `(z + i) / (z + i) = 1` for symbolic complex `z`.
Litex can verify it after establishing `z + i != 0`, but the current Lean
adapter has no reviewed conversion from that semantic non-equality evidence to
the native denominator proof used by field normalization. Powers are also
outside this adapter because the general compiler still gives `Pow` a narrower
rational representation.

## Generated example contract

The `.lit` file is authoritative. Compiler first executes it and receives the
exact recursive `StmtResult`; its native-carrier source construction validates
and consumes that Result directly. It does not reparse display text or search
for a Lean proof.
A same-name `.lean` file is committed so reviewers can inspect the translation
without running the tool. Every generated file imports the public `Litex`
umbrella exactly once.

The drift gate recompiles each `.lit` in memory, compares the output byte for
byte, and invokes Lean on the checked-in result. Unsupported successful Results fail
closed. The initial reviewed routes are equality-based membership transport,
the fingerprinted `order.less_equal_of_less` registered rule, and top-level
closed numeric equality through verifier-selected reflexivity or rational
normalization. Numeric expression WD facts remain named local Lean facts.

Statement scope is also part of this contract. A Litex `sketch` becomes an
isolated `__SketchNN` Lean namespace with a cloned incoming compiler context;
its new symbol and FactId bindings are discarded when emission returns to the
file scope. A direct top-level fact is not placed in that namespace.

## Dependency order

```text
Mathlib native carriers
  -> Core.lean                  [single semantic bridge header]
  -> private primitive/derived registries [closed representation rules]
  -> Same                       [public heterogeneous relation]
  -> Set                        [signature]
  -> In                         [definition: Same + Set.Carrier]
  -> Fn / fnSet                 [total unary proof-carrying carrier]
  -> FnWhere / fnSetWhere       [source-domain proposition retained]
  -> FnTelescope / fnTelescopeSet [one exact dependent source layer]
  -> fnApply / fnApplyOwn       [total checked application]
  -> fnApplyWhere variants      [membership + domain proof application]
  -> fnTelescopeApply variants  [all same-layer arguments + requirements]
  -> numeric sets N/Z/Q/R/C     [exact native-carrier definitions]
  -> adjacent numeric membership bridges [proved hierarchy projection]
  -> setBuilder                 [definition: subtype carrier]
  -> NPos                       [exact positive-natural subtype]
  -> RPos                       [exact positive-real subtype]
  -> ZStar/QStar/RStar/CStar    [certified complex-source subtypes]
  -> nonzero constructor/projection/widening/elimination rules [retained certificate]
  -> membership transport       [proof]
  -> AsReal                     [definition: Same + native real]
  -> Positive / Nonnegative    [canonical Mathlib-zero order]
  -> OrderValue                 [canonical Complex.re to native real]
  -> Lt / Le                    [custom relation reducing to Mathlib order]
  -> order transport/bridges    [proof, still owned by Core.lean]
  -> Rules.lean                 [concrete verifier-certificate theorems]
  -> Litex.lean                 [public umbrella import]
  -> verifier-produced statement IR [checked compilation evidence]
  -> compiler strict emitter    [reviewed adapters]
  -> proof/existential/object scopes [native values + explicit Litex evidence]
  -> concrete prop / set builder / choice [checked transport components]
  -> same-name generated examples [real Lean proof]
```

There are currently no project-declared axiom or trust edges. Core contains no
order coherence class or axiom; generic order transitivity is native Mathlib
transitivity over `OrderValue`. The native `ℝ`/`ℂ` examples retain Mathlib's foundational dependencies (`propext`,
`Classical.choice`, and `Quot.sound`). The next set-system decisions are
extensional set equality, union/intersection carriers, power-set universes,
and finiteness modulo `Same`.
