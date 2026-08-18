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

`Litex.Lt x y` and `Litex.Le x y` existentially select real representatives
and apply Mathlib's native `<` and `≤`. Both predicates transport across
`Same`. The rule `Lt x y → Le x y` needs no uniqueness assumption.

The core distinguishes choosing one representative from comparing two
independently selected representatives. `Litex.RealCoherence` remains the
explicit certificate shape consumed by the latter order theorems, and the
header postulates no inhabitant. Example 22's nonzero elimination avoids this
obligation by retaining the exact semantic nonzero certificate in the carrier.

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
`Litex.Lt (0 : ℂ) x` with that same real representative. The forall emitter
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
`{α : Type u} → (x : α) → Litex.In x s → S.Carrier`. A value is
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

The authoritative probe is `examples/4_FunctionSet.lit`. Its generated theorem
quantifies independent carriers for `x` and `f`, retains both membership
hypotheses, and emits both occurrences of `f(x)` with the exact
verifier-selected FactId/WD proofs. The nearest negative probe lives under
the compiler's function-set regression: changing `x s` to `x S` is rejected
by Litex before Lean emission.

The current construction boundary is one named real-valued unary layer.
Identity and expression trees built from the parameter, natural literals, and
`+`, `-`, `*`, `/` are compiled to the exact `ℝ` codomain carrier.
Checked reduction uses the closed native-operation `Same` congruence
theorems. Standalone anonymous compound functions, multiple parameters,
curried returns, other domains/codomains, and other operations remain
rejected.

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

Nearest rejected form: nonnegative multiplication. Verifier IR now retains
`MulNonnegative`, including recursive strategy and registered-rule children,
but `Litex.Le (0 : ℂ) a` and `Litex.Le (0 : ℂ) b` may select different native
real representatives for source zero. Multiplication needs those witnesses to
be identified before Mathlib's `mul_nonneg` applies. `Core.lean` exposes the
required `RealCoherence` certificate shape without installing an instance, so
compiler continues to fail closed rather than add an axiom or silently make
all generated theorems conditional on coherence.

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
operand facts, so emitter validates the target operator, set, and operands
instead of rediscovering a theorem.

Nearest rejected rational form: `a^z $in Q` for `a $in Q`, `z $in Z`. Its
operator-specific `Pow` certificate reaches IR, but the complex-valued source
power term and native exponent semantics have not received a reviewed compiler
contract. It therefore remains fail-closed.

## Generated example contract

The `.lit` file is authoritative. Compiler first verifies it and captures the
exact `LitexToLeanStatementIr`; its native-carrier emitter validates and
consumes that IR. It does not reparse display text or search for a Lean proof.
A same-name `.lean` file is committed so reviewers can inspect the translation
without running the tool. Every generated file imports the public `Litex`
umbrella exactly once.

The drift gate recompiles each `.lit` in memory, compares the output byte for
byte, and invokes Lean on the checked-in result. Unsupported verified IR fails
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
  -> fnApply / fnApplyOwn       [total checked application]
  -> fnApplyWhere variants      [membership + domain proof application]
  -> numeric sets N/Z/Q/R/C     [exact native-carrier definitions]
  -> adjacent numeric membership bridges [proved hierarchy projection]
  -> setBuilder                 [definition: subtype carrier]
  -> NPos                       [exact positive-natural subtype]
  -> RPos                       [exact positive-real subtype]
  -> ZStar/QStar/RStar/CStar    [certified complex-source subtypes]
  -> nonzero constructor/projection/widening/elimination rules [retained certificate]
  -> membership transport       [proof]
  -> AsReal                     [definition: Same + native real]
  -> RealCoherence              [certificate interface, no inhabitant assumed]
  -> Lt / Le                    [definition: native real order]
  -> order transport/bridges    [proof, still owned by Core.lean]
  -> Rules.lean                 [concrete verifier-certificate theorems]
  -> Litex.lean                 [public umbrella import]
  -> verifier-produced statement IR [checked compilation evidence]
  -> compiler strict emitter    [reviewed adapters]
  -> proof/existential/object scopes [native values + explicit Litex evidence]
  -> concrete prop / set builder / choice [checked transport components]
  -> same-name generated examples [real Lean proof]
```

There are currently no project-declared axiom or trust edges. A theorem may
take `RealCoherence` as an ordinary explicit typeclass parameter; that is not a
header axiom and remains visible in the generated theorem signature. The native
`ℝ`/`ℂ` examples retain Mathlib's foundational dependencies (`propext`,
`Classical.choice`, and `Quot.sound`). The next set-system decisions are
extensional set equality, union/intersection carriers, power-set universes,
and finiteness modulo `Same`.
