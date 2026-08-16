# Litex-to-Lean executable feature ledger

This file records the currently supported Litex-to-Lean mappings. Each section
contains a self-contained Litex program, the complete Lean file actually
emitted by the current compiler, a compact required shape, and the nearest
rejected boundary. The required shape summarizes the output; it is not a
substitute for the complete generated file.

Generated output uses ABI version 9 and one `Litex.Object` universe. No entry
may reintroduce native numeric binders, `Set ℝ`, carrier unification, widening,
downcasts, target-side proof search, `sorry`, or a compiler-invented axiom.

## well_defined_object_dag

This first entry records verifier-owned well-defined object identities. The two
inner applications' WD evidence must be replayed before the outer application
evidence inside the theorem proof, and the two equal source occurrences must
reuse the same frozen outer object identity.

```litex
forall a, b R, g fn(x R) R, t fn(x R) R, f fn(x, y R) R:
    f(g(a), t(b)) = f(g(a), t(b))
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: well_defined_object_dag -->
```lean
import Litex.Rules

theorem __fact43 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) (b : Litex.Object) (__h0_2 : Litex.In b Litex.R) (g : Litex.Object) (__h0_3 : Litex.In g (Litex.fnSpace1 Litex.R Litex.R)) (t : Litex.Object) (__h0_4 : Litex.In t (Litex.fnSpace1 Litex.R Litex.R)) (f : Litex.Object) (__h0_5 : Litex.In f (Litex.fnSpace2 Litex.R Litex.R Litex.R)), (f [(g [a]), (t [b])]) = (f [(g [a]), (t [b])]) :=
by
  intro a __h0_1 b __h0_2 g __h0_3 t __h0_4 f __h0_5
  have __wd0_7 : Litex.In a Litex.R := by
    exact (__h0_1)
  have __obj44_app : Litex.Applicable (g) [a] := by
    exact (Litex.fnSpaceApplicable (args := [a]) __h0_3 rfl (by
      change ∃ __h_arg0 : Litex.In (a) Litex.R, True
      exact Exists.intro (__wd0_7) (True.intro)))
  have __obj44_result : Litex.In (g [a]) Litex.R := by
    exact (by simpa using (Litex.fnSpaceResult (args := [a]) __h0_3 rfl (by
      change ∃ __h_arg0 : Litex.In (a) Litex.R, True
      exact Exists.intro (__wd0_7) (True.intro))))
  have __wd0_8 : Litex.In b Litex.R := by
    exact (__h0_2)
  have __obj45_app : Litex.Applicable (t) [b] := by
    exact (Litex.fnSpaceApplicable (args := [b]) __h0_4 rfl (by
      change ∃ __h_arg0 : Litex.In (b) Litex.R, True
      exact Exists.intro (__wd0_8) (True.intro)))
  have __obj45_result : Litex.In (t [b]) Litex.R := by
    exact (by simpa using (Litex.fnSpaceResult (args := [b]) __h0_4 rfl (by
      change ∃ __h_arg0 : Litex.In (b) Litex.R, True
      exact Exists.intro (__wd0_8) (True.intro))))
  have __wd0_9 : Litex.In g (Litex.fnSpace1 Litex.R Litex.R) := by
    exact (__h0_3)
  have __wd0_10 : Litex.In (g [a]) Litex.R := by
    exact ((by simpa using (Litex.fnSpaceResult (args := [a]) __h0_3 rfl (by
      change ∃ __h_arg0 : Litex.In (a) Litex.R, True
      exact Exists.intro (__wd0_7) (True.intro)))))
  have __wd0_11 : Litex.In t (Litex.fnSpace1 Litex.R Litex.R) := by
    exact (__h0_4)
  have __wd0_12 : Litex.In (t [b]) Litex.R := by
    exact ((by simpa using (Litex.fnSpaceResult (args := [b]) __h0_4 rfl (by
      change ∃ __h_arg0 : Litex.In (b) Litex.R, True
      exact Exists.intro (__wd0_8) (True.intro)))))
  have __obj46_app : Litex.Applicable (f) [(g [a]), (t [b])] := by
    exact (Litex.fnSpaceApplicable (args := [(g [a]), (t [b])]) __h0_5 rfl (by
      change ∃ __h_arg0 : Litex.In ((g [a])) Litex.R, ∃ __h_arg1 : Litex.In ((t [b])) Litex.R, True
      exact Exists.intro (__wd0_10) (Exists.intro (__wd0_12) (True.intro))))
  have __obj46_result : Litex.In (f [(g [a]), (t [b])]) Litex.R := by
    exact (by simpa using (Litex.fnSpaceResult (args := [(g [a]), (t [b])]) __h0_5 rfl (by
      change ∃ __h_arg0 : Litex.In ((g [a])) Litex.R, ∃ __h_arg1 : Litex.In ((t [b])) Litex.R, True
      exact Exists.intro (__wd0_10) (Exists.intro (__wd0_12) (True.intro)))))
  exact rfl
```
<!-- END ACTUAL GENERATED LEAN: well_defined_object_dag -->

Required generated shape:

```lean
theorem __fact... :
    ∀ ...
      (g : Litex.Object) (__h0_3 : Litex.In g (Litex.fnSpace1 Litex.R Litex.R))
      (f : Litex.Object) (__h0_5 : Litex.In f (Litex.fnSpace2 Litex.R Litex.R Litex.R)),
      f [g [a], t [b]] = f [g [a], t [b]] := by
  intro a __h0_1 b __h0_2 g __h0_3 t __h0_4 f __h0_5
  have __obj<g>_app : Litex.Applicable g [a] := ...
  have __obj<g>_result : Litex.In (g [a]) Litex.R := ...
  have __obj<t>_app : Litex.Applicable t [b] := ...
  have __obj<t>_result : Litex.In (t [b]) Litex.R := ...
  have __obj<outer>_app : Litex.Applicable f [g [a], t [b]] := ...
  exact rfl
```

Each selected `WellDefinedObjId` owns stable local applicability/result names,
and verifier propositions remain separately named by
`__wd<environment-depth>_<WellDefinedFactId>`. All compiler-owned names use
the Litex-reserved `__` prefix. The emitter follows the retained
child roles and order; it does not reconstruct the application DAG from
rendered source text or emit generalized WD declarations above the theorem.

Boundary: this entry covers one lexical `forall` environment. A child may see
parent WD evidence, but evidence from a closed child environment must not leak
outward. Function-valued bodyless `have` and `trust have` remain separate
unsupported statement forms.

## trusted_forall_atomic_fact

An `abstract_prop` introduces one uninterpreted predicate. The explicit trusted
universal fact becomes one target axiom, while its concrete atomic instance is
a theorem that cites that exact retained `FactId` and supplies the checked
membership proof in argument order.

```litex
abstract_prop p(x)

trust forall x R:
    $p(x)

$p(1)
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: trusted_forall_atomic_fact -->
```lean
import Litex.Rules

axiom p : Litex.Object → Prop

axiom __fact3 : ∀ (x : Litex.Object) (__h0_1 : Litex.In x Litex.R), p x

theorem __fact4 : p 1 := by
  exact (__fact3 1 (Litex.Rules.numeralInR 1))
```
<!-- END ACTUAL GENERATED LEAN: trusted_forall_atomic_fact -->

Required generated shape:

```lean
axiom p : Litex.Object → Prop
axiom __fact... :
  ∀ (x : Litex.Object) (_ : Litex.In x Litex.R), p x

theorem __fact... : p 1 := by
  exact (fact... 1 (Litex.Rules.numeralInR 1))
```

The parentheses around the membership proof are semantically required: the
Lean elaborator must receive the applied theorem
`Litex.Rules.numeralInR 1`, not the unapplied theorem family. An
unavailable or changed source `FactId` fails emission rather than falling back
to proposition matching or `assumption`.

Boundary: `abstract_prop q(x)` followed by `$q(1)` remains rejected when no
known universal fact proves the application. The compiler must not turn that
atomic fact into another axiom.

## proof_carrying_arithmetic

Division is a partial Litex object constructor. Its target term consumes the
same three facts selected by source well-definedness: numerator membership in
`C`, denominator membership in `C`, and denominator nonzero. The quotient's
checked complex-closure fact is named before the enclosing addition cites it.

```litex
forall a, b, c C:
    (a + b) + c = (a + b) + c

forall a, b, c C:
    ((a - b) * c) + a = ((a - b) * c) + a
forall a, b C:
    b != 0
    =>:
        a / b = a / b

forall a, b C:
    b != 0
    =>:
        (a / b) + a = (a / b) + a

forall a, b R:
    b != 0
    =>:
        a / b $in R
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: proof_carrying_arithmetic -->
```lean
import Litex.Rules

theorem __fact13 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.C) (b : Litex.Object) (__h0_2 : Litex.In b Litex.C) (c : Litex.Object) (__h0_3 : Litex.In c Litex.C), (Litex.add (Litex.add a b) c) = (Litex.add (Litex.add a b) c) :=
by
  intro a __h0_1 b __h0_2 c __h0_3
  have __wd0_5 : Litex.In a Litex.C := by
    exact (__h0_1)
  have __wd0_6 : Litex.In b Litex.C := by
    exact (__h0_2)
  have __wd0_7 : Litex.In (Litex.add a b) Litex.C := by
    exact ((Litex.Rules.complexAddClosure (__wd0_5) (__wd0_6)))
  have __wd0_8 : Litex.In c Litex.C := by
    exact (__h0_3)
  have __obj12_result : Litex.In (Litex.add (Litex.add a b) c) Litex.C := by
    exact ((Litex.Rules.complexAddClosure (__wd0_7) (__wd0_8)))
  exact rfl

theorem __fact26 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.C) (b : Litex.Object) (__h0_2 : Litex.In b Litex.C) (c : Litex.Object) (__h0_3 : Litex.In c Litex.C), (Litex.add (Litex.mul (Litex.sub a b) c) a) = (Litex.add (Litex.mul (Litex.sub a b) c) a) :=
by
  intro a __h0_1 b __h0_2 c __h0_3
  have __wd0_19 : Litex.In a Litex.C := by
    exact (__h0_1)
  have __wd0_20 : Litex.In b Litex.C := by
    exact (__h0_2)
  have __wd0_21 : Litex.In (Litex.sub a b) Litex.C := by
    exact ((Litex.Rules.complexSubClosure (__wd0_19) (__wd0_20)))
  have __wd0_22 : Litex.In c Litex.C := by
    exact (__h0_3)
  have __wd0_23 : Litex.In (Litex.mul (Litex.sub a b) c) Litex.C := by
    exact ((Litex.Rules.complexMulClosure (__wd0_21) (__wd0_22)))
  have __wd0_24 : Litex.In a Litex.C := by
    exact (__h0_1)
  have __obj32_result : Litex.In (Litex.add (Litex.mul (Litex.sub a b) c) a) Litex.C := by
    exact ((Litex.Rules.complexAddClosure (__wd0_23) (__wd0_24)))
  exact rfl

theorem __fact39 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.C) (b : Litex.Object) (__h0_2 : Litex.In b Litex.C) (__h0_3 : b ≠ 0), (Litex.div a b) = (Litex.div a b) :=
by
  intro a __h0_1 b __h0_2 __h0_3
  have __wd0_34 : b ≠ 0 := by
    exact (__h0_3)
  have __wd0_35 : Litex.In a Litex.C := by
    exact (__h0_1)
  have __wd0_36 : Litex.In b Litex.C := by
    exact (__h0_2)
  have __obj49_result : Litex.In (Litex.div a b) Litex.C := by
    exact ((Litex.Rules.complexDivClosure (__wd0_35) (__wd0_36) (__wd0_34)))
  exact rfl

theorem __fact52 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.C) (b : Litex.Object) (__h0_2 : Litex.In b Litex.C) (__h0_3 : b ≠ 0), (Litex.add (Litex.div a b) a) = (Litex.add (Litex.div a b) a) :=
by
  intro a __h0_1 b __h0_2 __h0_3
  have __wd0_45 : b ≠ 0 := by
    exact (__h0_3)
  have __wd0_46 : Litex.In a Litex.C := by
    exact (__h0_1)
  have __wd0_47 : Litex.In b Litex.C := by
    exact (__h0_2)
  have __wd0_48 : Litex.In (Litex.div a b) Litex.C := by
    exact ((Litex.Rules.complexDivClosure (__wd0_46) (__wd0_47) (__wd0_45)))
  have __wd0_49 : Litex.In a Litex.C := by
    exact (__h0_1)
  have __obj66_result : Litex.In (Litex.add (Litex.div a b) a) Litex.C := by
    exact ((Litex.Rules.complexAddClosure (__wd0_48) (__wd0_49)))
  exact rfl

theorem __fact65 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) (b : Litex.Object) (__h0_2 : Litex.In b Litex.R) (__h0_3 : b ≠ 0), Litex.In (Litex.div a b) Litex.R :=
by
  intro a __h0_1 b __h0_2 __h0_3
  have __wd0_60 : b ≠ 0 := by
    exact (__h0_3)
  have __wd0_61 : Litex.In a Litex.R := by
    exact (__h0_1)
  have __wd0_62 : Litex.In a Litex.C := by
    exact ((Litex.Rules.realInComplex (__h0_1)))
  have __wd0_63 : Litex.In b Litex.R := by
    exact (__h0_2)
  have __wd0_64 : Litex.In b Litex.C := by
    exact ((Litex.Rules.realInComplex (__h0_2)))
  have __obj84_result : Litex.In (Litex.div a b) Litex.C := by
    exact ((Litex.Rules.complexDivClosure (__wd0_62) (__wd0_64) (__wd0_60)))
  exact (Litex.Rules.realDivClosure (__wd0_62) (__wd0_64) (__wd0_60) (__h0_1) (__h0_2))
```
<!-- END ACTUAL GENERATED LEAN: proof_carrying_arithmetic -->

Required generated shape:

```lean
theorem __fact... : Litex.add (Litex.div a b) a =
    Litex.add (Litex.div a b) a := by
  intro a h_a b h_b h_nonzero
  have __wd0_<a_in_C> : Litex.In a Litex.C := by exact h_a
  have __wd0_<b_in_C> : Litex.In b Litex.C := by exact h_b
  have __wd0_<b_ne_zero> : b ≠ 0 := by exact h_nonzero
  have __wd0_<quotient_in_C> : Litex.In (Litex.div a b) Litex.C := by
    exact Litex.Rules.complexDivClosure
      __wd0_<a_in_C> __wd0_<b_in_C> __wd0_<b_ne_zero>
  exact rfl
```

Boundary: deleting, duplicating, misindexing, or retargeting any of the three
division requirements fails before Lean emission. The proof-free target term
`Litex.div a b` does not authorize source emission without those three exact
certificate slots.

## inferred_forall_premise

The parameter `x R+` contributes one ordinary membership binder. Litex then
infers `0 < x`; To-Lean emits that verifier-selected route as a local theorem,
registers its exact `FactId`, and cites it when replaying the surface-equivalent
conclusion `x > 0`.

```litex
forall x R+:
    x > 0
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: inferred_forall_premise -->
```lean
import Litex.Rules

theorem __fact16 : ∀ (x : Litex.Object) (__h0_1 : Litex.In x Litex.RPos), Litex.Lt 0 x :=
by
  intro x __h0_1
  have __inferred0 : Litex.Lt 0 x := by
    exact (Litex.Rules.positiveRealMembership __h0_1)
  exact __inferred0
```
<!-- END ACTUAL GENERATED LEAN: inferred_forall_premise -->

Required generated shape:

```lean
theorem __fact... :
    ∀ (x : Litex.Object) (__h0_1 : Litex.In x Litex.RPos), Litex.Lt 0 x := by
  intro x __h0_1
  have __inferred0 : Litex.Lt 0 x := by
    exact Litex.Rules.positiveRealMembership __h0_1
  exact __inferred0
```

`positiveRealMembership` is an ordinary checked theorem over the shared core's
`inRPos_iff`; the generated file neither retypes `x` as a Lean real nor asks
Lean to search for positivity. The local inferred name is registered only
after its proof renders, so a malformed self-reference cannot pass emission.

Boundary: changing the certificate's source `FactId` to an unavailable ID
fails closed. The distinct inference chain behind `forall x N+: x > 0` remains
unsupported until each of its verifier-selected steps has a checked adapter.

## proof_carrying_list_set

A finite set literal consumes the exact WD construction recipe checked by
Litex: one ordered child object per source entry and one indexed inequality for
every pair `i < j`. The emitter names every child and every retained fact, then
builds `ListSetWellDefined` without searching for distinctness in Lean.

```litex
forall a, b set:
    a != b
    =>:
        {a, b} = {a, b}

forall a, b, c set:
    a != b
    a != c
    b != c
    =>:
        {a, b, c} = {a, b, c}
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: proof_carrying_list_set -->
```lean
import Litex.Rules

theorem __fact13 : ∀ (a : Litex.Object) (__h0_1 : Litex.IsSet a) (b : Litex.Object) (__h0_2 : Litex.IsSet b) (__h0_3 : a ≠ b), (Litex.listSet [a, b]) = (Litex.listSet [a, b]) :=
by
  intro a __h0_1 b __h0_2 __h0_3
  have __wd0_2 : a ≠ b := by
    exact (__h0_3)
  exact rfl

theorem __fact35 : ∀ (a : Litex.Object) (__h0_1 : Litex.IsSet a) (b : Litex.Object) (__h0_2 : Litex.IsSet b) (c : Litex.Object) (__h0_3 : Litex.IsSet c) (__h0_4 : a ≠ b) (__h0_5 : a ≠ c) (__h0_6 : b ≠ c), (Litex.listSet [a, b, c]) = (Litex.listSet [a, b, c]) :=
by
  intro a __h0_1 b __h0_2 c __h0_3 __h0_4 __h0_5 __h0_6
  have __wd0_7 : a ≠ b := by
    exact (__h0_4)
  have __wd0_8 : a ≠ c := by
    exact (__h0_5)
  have __wd0_9 : b ≠ c := by
    exact (__h0_6)
  exact rfl
```
<!-- END ACTUAL GENERATED LEAN: proof_carrying_list_set -->

Lean status: **checked** — the theorem type uses proof-free `Litex.listSet`
terms and its pairwise WD evidence is introduced locally after `intro`.

Required generated shape:

```lean
theorem __fact... : Litex.listSet [a, b, c] = Litex.listSet [a, b, c] := by
  intro a h_a b h_b c h_c h_ab h_ac h_bc
  have __wd0_<a_ne_b> : a ≠ b := by exact h_ab
  have __wd0_<a_ne_c> : a ≠ c := by exact h_ac
  have __wd0_<b_ne_c> : b ≠ c := by exact h_bc
  exact rfl
```

The source-order matrix is exact: `(0,1)` cites `a ≠ b`, `(0,2)` cites
`a ≠ c`, and `(1,2)` cites `b ≠ c`. Missing, duplicated, reversed,
out-of-range, or retargeted roles fail before Lean emission. Proof-free target
denotation does not make a list literal with a missing source WD certificate
valid Litex.

## object_choice

This entry adds one noncomputable object from the verifier-owned nonempty-set
proof.

```litex
have x R
x $in R
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: object_choice -->
```lean
import Litex.Rules

noncomputable def x : Litex.Object := Classical.choose (Litex.Rules.realSetNonempty)

theorem __fact3 : Litex.In x Litex.R := by
  unfold x
  exact Classical.choose_spec (Litex.Rules.realSetNonempty)
```
<!-- END ACTUAL GENERATED LEAN: object_choice -->

Lean uses `Classical.choose` and `choose_spec`; changed carrier or nonemptiness
evidence is rejected instead of inventing a witness.

```lean
noncomputable def x : Litex.Object := Classical.choose <nonempty_R>
theorem __fact_<x_in_R> : Litex.In x Litex.R := Classical.choose_spec <nonempty_R>
```

## existential_intro_elim

Existential introduction and elimination replay the ordered type and body
projections.

```litex
witness exist x R st {x = 1} from 1:
    1 = 1
obtain y from exist x R st {x = 1}
y = 1
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: existential_intro_elim -->
```lean
import Litex.Rules

theorem __fact8 : ∃ (x : Litex.Object), Litex.In x Litex.R ∧ x = 1 := by
  exact (by
  have __exist_step1 : (1 : Litex.Object) = 1 := by
    exact rfl
  exact ⟨1, (Litex.Rules.numeralInR 1), (__exist_step1)⟩)

noncomputable def y : Litex.Object := Classical.choose (__fact8)

theorem __fact13 : Litex.In y Litex.R := by
  unfold y
  exact (Classical.choose_spec (__fact8)).1

theorem __fact14 : y = 1 := by
  unfold y
  exact (Classical.choose_spec (__fact8)).2
```
<!-- END ACTUAL GENERATED LEAN: existential_intro_elim -->

Lean uses `Exists.intro`, `Classical.choose`, and `choose_spec`; `exist!`,
negation, and changed projection roles remain rejected boundaries.

```lean
theorem __fact_<exist> : ∃ x, Litex.In x Litex.R ∧ x = 1 := by ...
noncomputable def y : Litex.Object := Classical.choose __fact<exist>
theorem __fact_<y_in_R> : Litex.In y Litex.R := (Classical.choose_spec __fact<exist>).1
```

## case_and_contradiction_scopes

Case analysis and contradiction keep case and reverse-assumption `FactId`s
local.

```litex
by cases:
    ? 1 = 1
    case 1 = 1:
        2 = 2
by contra:
    ? 2 = 2
    1 = 1
    impossible 2 != 2
by cases:
    ? 4 = 4
    case 3 = 3 and 4 = 4:
        3 = 3
by contra:
    ? 5 != 6
    impossible 5 = 6
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: case_and_contradiction_scopes -->
```lean
import Litex.Rules

theorem __fact3 : (1 : Litex.Object) = 1 := by
  exact (by
  have __case1 : (1 : Litex.Object) = 1 := rfl
  have __case1_step_1 : (2 : Litex.Object) = 2 := by
    exact (rfl)
  exact __case1)

theorem __fact5 : (2 : Litex.Object) = 2 := by
  exact (by
  classical
  by_contra __reverse
  have __contra_step_1 : (1 : Litex.Object) = 1 := by
    exact (rfl)
  exact ((__reverse) : (2 : Litex.Object) ≠ 2) (rfl))

theorem __fact9 : (4 : Litex.Object) = 4 := by
  exact (by
  have __case1 : (3 : Litex.Object) = 3 ∧ ((4 : Litex.Object) = 4) := And.intro (rfl) ((rfl))
  have __case1_step_1 : (3 : Litex.Object) = 3 := by
    exact (((__case1)).1)
  have __case1_step_2 : (4 : Litex.Object) = 4 := by
    exact (((__case1)).2)
  have __case1_step_3 : (3 : Litex.Object) = 3 := by
    exact (rfl)
  exact __case1_step_2)

theorem __fact11 : (5 : Litex.Object) ≠ 6 := by
  exact (by
  classical
  exact Classical.byContradiction (fun __negated_goal => by
    have __reverse : (5 : Litex.Object) = 6 := Classical.byContradiction (fun __not_reverse => __negated_goal __not_reverse)
    exact (((by
  exact (Litex.Rules.numeralNe 5 6).2 (by norm_num))) : (5 : Litex.Object) ≠ 6) (__reverse)))
```
<!-- END ACTUAL GENERATED LEAN: case_and_contradiction_scopes -->

A local `FactId` moved to another coverage slot fails closed. Conjuncts are
introduced/projected in their exact source order, and a negative target uses
an explicit classical double-negation bridge.

```lean
have __case1 : <case proposition> := <coverage proof>
exact Classical.byContradiction (fun __negated_goal => by
have __reverse : <positive reverse assumption> := Classical.byContradiction ...
```

## named_theorem

A named theorem makes the source name own the complete universal fact.

```litex
thm one_eq_one:
    ? forall:
        1 = 1
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: named_theorem -->
```lean
import Litex.Rules

theorem one_eq_one : (1 : Litex.Object) = 1 :=
by
  exact rfl
```
<!-- END ACTUAL GENERATED LEAN: named_theorem -->

Lean emits `theorem one_eq_one`, not a duplicate `fact_N`; changed proof-step
count or order is rejected.

```lean
theorem one_eq_one : 1 = 1 := by
  exact rfl
```

## total_object_constructors

This entry adds a closed constant and total binary set constructor.

```litex
pi = pi
forall A, B set:
    union(A, B) = union(A, B)
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: total_object_constructors -->
```lean
import Litex.Rules

theorem __fact1 : Litex.pi = Litex.pi := by
  exact rfl

theorem __fact11 : ∀ (A : Litex.Object) (__h0_1 : Litex.IsSet A) (B : Litex.Object) (__h0_2 : Litex.IsSet B), (Litex.union A B) = (Litex.union A B) :=
by
  intro A __h0_1 B __h0_2
  exact rfl
```
<!-- END ACTUAL GENERATED LEAN: total_object_constructors -->

`Litex.pi` and `Litex.union A B` need no proof arguments. Unsupported constants
and changed arity remain explicit errors.

```lean
theorem __fact_<pi> : Litex.pi = Litex.pi := by rfl
theorem __fact_<union> ... : Litex.union A B = Litex.union A B := by rfl
```

## proof_carrying_division

This entry isolates the partial division contract.

```litex
forall a, b C:
    b != 0
    =>:
        a / b = a / b
forall a, b R:
    b != 0
    =>:
        a / b $in R
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: proof_carrying_division -->
```lean
import Litex.Rules

theorem __fact13 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.C) (b : Litex.Object) (__h0_2 : Litex.In b Litex.C) (__h0_3 : b ≠ 0), (Litex.div a b) = (Litex.div a b) :=
by
  intro a __h0_1 b __h0_2 __h0_3
  have __wd0_4 : b ≠ 0 := by
    exact (__h0_3)
  have __wd0_5 : Litex.In a Litex.C := by
    exact (__h0_1)
  have __wd0_6 : Litex.In b Litex.C := by
    exact (__h0_2)
  have __obj10_result : Litex.In (Litex.div a b) Litex.C := by
    exact ((Litex.Rules.complexDivClosure (__wd0_5) (__wd0_6) (__wd0_4)))
  exact rfl

theorem __fact26 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) (b : Litex.Object) (__h0_2 : Litex.In b Litex.R) (__h0_3 : b ≠ 0), Litex.In (Litex.div a b) Litex.R :=
by
  intro a __h0_1 b __h0_2 __h0_3
  have __wd0_15 : b ≠ 0 := by
    exact (__h0_3)
  have __wd0_16 : Litex.In a Litex.R := by
    exact (__h0_1)
  have __wd0_17 : Litex.In a Litex.C := by
    exact ((Litex.Rules.realInComplex (__h0_1)))
  have __wd0_18 : Litex.In b Litex.R := by
    exact (__h0_2)
  have __wd0_19 : Litex.In b Litex.C := by
    exact ((Litex.Rules.realInComplex (__h0_2)))
  have __obj27_result : Litex.In (Litex.div a b) Litex.C := by
    exact ((Litex.Rules.complexDivClosure (__wd0_17) (__wd0_19) (__wd0_15)))
  exact (Litex.Rules.realDivClosure (__wd0_17) (__wd0_19) (__wd0_15) (__h0_1) (__h0_2))
```
<!-- END ACTUAL GENERATED LEAN: proof_carrying_division -->

The Litex source certificate retains two `C` memberships and the exact nonzero
proof; none of the three slots can be deleted, moved, or reconstructed by
target search. The quotient term itself is proof-free.

```lean
theorem __fact... : Litex.div a b = Litex.div a b := by
  intro a h_a b h_b h_nonzero
  have wd_<a_in_C> : Litex.In a Litex.C := ...
  have wd_<b_in_C> : Litex.In b Litex.C := ...
  have wd_<b_ne_zero> : b ≠ 0 := by exact h_nonzero
  exact rfl
```

## set_builder_scope

A set builder owns its predicate binder by `SymbolId`.

```litex
have S set = {x R: x = x}
S = S
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: set_builder_scope -->
```lean
import Litex.Rules

noncomputable def S : Litex.Object := (Litex.setBuilder Litex.R (fun __x2 => __x2 = __x2))

theorem __fact4 : Litex.IsSet S := by
  simpa only [S] using (Litex.Rules.objectIsSet (Litex.setBuilder Litex.R (fun __x2 => __x2 = __x2)))

theorem __fact5 : S = (Litex.setBuilder Litex.R (fun __x2 => __x2 = __x2)) := by
  rfl

theorem __fact6 : S = S := by
  exact rfl
```
<!-- END ACTUAL GENERATED LEAN: set_builder_scope -->

Lean emits `Litex.setBuilder ... (fun __xID => ...)`; the local
binder never leaks and changed identity changes the retained object.

```lean
noncomputable def S : Litex.Object :=
  Litex.setBuilder Litex.R (fun __x<id> =>
    __x<id> = __x<id>)
```

## named_function

A named function emits a dependent requirements telescope, verifier-owned
local `__wd<environment-depth>_<WellDefinedFactId>` body DAG inside its closure
proof, range membership, definition, and exact replay. `inc` exercises
proof-free addition with local WD; `reciprocal` reuses its retained domain fact
beside proof-free division.

```litex
have fn id(x R) R = x
id(1) = 1

have fn inc(x R) R = x + 1
inc(1) = 1 + 1

have fn reciprocal(x R: x != 0) R = 1 / x
forall a R:
    a != 0
    =>:
        reciprocal(a) = 1 / a
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: named_function -->
```lean
import Litex.Rules

noncomputable def __litex_id_spec : Litex.FnSpec :=
  ({ arity := 1, requirements := fun __fn_arg => ∃ __h_arg0 : Litex.In (Litex.arg __fn_arg 0) Litex.R, True, range := fun __fn_arg __fn_arg_len __fn_arg_req => Litex.R } : Litex.FnSpec)

noncomputable def __litex_id_body
    (__fn_arg : List Litex.Object)
    (__fn_arg_len : __fn_arg.length = __litex_id_spec.arity)
    (__fn_arg_req : __litex_id_spec.requirements __fn_arg) : Litex.Object :=
  (Litex.arg __fn_arg 0)

theorem __litex_id_closed :
    ∀ __fn_arg __fn_arg_len __fn_arg_req,
      Litex.In
        (__litex_id_body __fn_arg __fn_arg_len __fn_arg_req)
        (__litex_id_spec.range __fn_arg __fn_arg_len __fn_arg_req) := by
  intro __fn_arg __fn_arg_len __fn_arg_req
  change Litex.In (Litex.arg __fn_arg 0) Litex.R
  exact Exists.choose (__fn_arg_req)

noncomputable def __litex_id_impl : Litex.Object :=
  Litex.functionObject __litex_id_spec __litex_id_body

noncomputable def litex_id : Litex.Object := __litex_id_impl

theorem __fact5 : Litex.In litex_id (Litex.FnSet ({ arity := 1, requirements := fun __fn_arg => ∃ __h_arg0 : Litex.In (Litex.arg __fn_arg 0) Litex.R, True, range := fun __fn_arg __fn_arg_len __fn_arg_req => Litex.R } : Litex.FnSpec)) := by
  simpa only [litex_id, __litex_id_impl, __litex_id_spec] using
    (Litex.functionObjectInFnSet __litex_id_spec __litex_id_body __litex_id_closed)

theorem __fact6 : litex_id = __litex_id_impl := by
  rfl

theorem __fact7 : (litex_id [1]) = 1 := by
  have __wd0_2 : Litex.In 1 Litex.R := by
    exact (Litex.Rules.numeralInR 1)
  have __obj15_app : Litex.Applicable (litex_id) [1] := by
    exact (Litex.fnSetApplicable (args := [1]) __fact5 rfl (by
      change ∃ __h_arg0 : Litex.In (1) Litex.R, True
      exact Exists.intro (__wd0_2) (True.intro)))
  have __obj15_result : Litex.In (litex_id [1]) Litex.R := by
    exact (by simpa using (Litex.fnSetResult (args := [1]) __fact5 rfl (by
      change ∃ __h_arg0 : Litex.In (1) Litex.R, True
      exact Exists.intro (__wd0_2) (True.intro))))
  exact (by
  change ((litex_id) [1]) = 1
  rw [__fact6]
  unfold __litex_id_impl
  rw [Litex.functionObject_apply _ _ _ (by
    simpa only [__fact6, __litex_id_impl] using __obj15_app)]
  simp only [__litex_id_body, Litex.arg, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil])

noncomputable def __inc_spec : Litex.FnSpec :=
  ({ arity := 1, requirements := fun __fn_arg => ∃ __h_arg0 : Litex.In (Litex.arg __fn_arg 0) Litex.R, True, range := fun __fn_arg __fn_arg_len __fn_arg_req => Litex.R } : Litex.FnSpec)

noncomputable def __inc_body
    (__fn_arg : List Litex.Object)
    (__fn_arg_len : __fn_arg.length = __inc_spec.arity)
    (__fn_arg_req : __inc_spec.requirements __fn_arg) : Litex.Object :=
  (Litex.add (Litex.arg __fn_arg 0) 1)

theorem __inc_closed :
    ∀ __fn_arg __fn_arg_len __fn_arg_req,
      Litex.In
        (__inc_body __fn_arg __fn_arg_len __fn_arg_req)
        (__inc_spec.range __fn_arg __fn_arg_len __fn_arg_req) := by
  intro __fn_arg __fn_arg_len __fn_arg_req
  have __wd0_8 : Litex.In (Litex.arg __fn_arg 0) Litex.R := by
    exact (Exists.choose (__fn_arg_req))
  have __wd0_9 : Litex.In (Litex.arg __fn_arg 0) Litex.C := by
    exact ((Litex.Rules.realInComplex (Exists.choose (__fn_arg_req))))
  have __wd0_10 : Litex.In 1 Litex.C := by
    exact (Litex.Rules.numeralInC 1)
  have __obj24_result : Litex.In (Litex.add (Litex.arg __fn_arg 0) 1) Litex.C := by
    exact ((Litex.Rules.complexAddClosure (__wd0_9) (__wd0_10)))
  change Litex.In (Litex.add (Litex.arg __fn_arg 0) 1) Litex.R
  exact (Litex.Rules.realAddClosure (__wd0_9) (__wd0_10) (Exists.choose (__fn_arg_req)) (Litex.Rules.numeralInR 1))

noncomputable def __inc_impl : Litex.Object :=
  Litex.functionObject __inc_spec __inc_body

noncomputable def inc : Litex.Object := __inc_impl

theorem __fact12 : Litex.In inc (Litex.FnSet ({ arity := 1, requirements := fun __fn_arg => ∃ __h_arg0 : Litex.In (Litex.arg __fn_arg 0) Litex.R, True, range := fun __fn_arg __fn_arg_len __fn_arg_req => Litex.R } : Litex.FnSpec)) := by
  simpa only [inc, __inc_impl, __inc_spec] using
    (Litex.functionObjectInFnSet __inc_spec __inc_body __inc_closed)

theorem __fact13 : inc = __inc_impl := by
  rfl

theorem __fact14 : (inc [1]) = (Litex.add 1 1) := by
  have __wd0_11 : Litex.In 1 Litex.R := by
    exact (Litex.Rules.numeralInR 1)
  have __obj28_app : Litex.Applicable (inc) [1] := by
    exact (Litex.fnSetApplicable (args := [1]) __fact12 rfl (by
      change ∃ __h_arg0 : Litex.In (1) Litex.R, True
      exact Exists.intro (__wd0_11) (True.intro)))
  have __obj28_result : Litex.In (inc [1]) Litex.R := by
    exact (by simpa using (Litex.fnSetResult (args := [1]) __fact12 rfl (by
      change ∃ __h_arg0 : Litex.In (1) Litex.R, True
      exact Exists.intro (__wd0_11) (True.intro))))
  have __wd0_12 : Litex.In 1 Litex.C := by
    exact (Litex.Rules.numeralInC 1)
  have __obj30_result : Litex.In (Litex.add 1 1) Litex.C := by
    exact ((Litex.Rules.complexAddClosure (__wd0_12) (__wd0_12)))
  exact (by
  change ((inc) [1]) = (Litex.add 1 1)
  rw [__fact13]
  unfold __inc_impl
  rw [Litex.functionObject_apply _ _ _ (by
    simpa only [__fact13, __inc_impl] using __obj28_app)]
  simp only [__inc_body, Litex.arg, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil])

noncomputable def __reciprocal_spec : Litex.FnSpec :=
  ({ arity := 1, requirements := fun __fn_arg => ∃ __h_arg0 : Litex.In (Litex.arg __fn_arg 0) Litex.R, ∃ __h_dom0 : (Litex.arg __fn_arg 0) ≠ 0, True, range := fun __fn_arg __fn_arg_len __fn_arg_req => Litex.R } : Litex.FnSpec)

noncomputable def __reciprocal_body
    (__fn_arg : List Litex.Object)
    (__fn_arg_len : __fn_arg.length = __reciprocal_spec.arity)
    (__fn_arg_req : __reciprocal_spec.requirements __fn_arg) : Litex.Object :=
  (Litex.div 1 (Litex.arg __fn_arg 0))

theorem __reciprocal_closed :
    ∀ __fn_arg __fn_arg_len __fn_arg_req,
      Litex.In
        (__reciprocal_body __fn_arg __fn_arg_len __fn_arg_req)
        (__reciprocal_spec.range __fn_arg __fn_arg_len __fn_arg_req) := by
  intro __fn_arg __fn_arg_len __fn_arg_req
  have __wd0_19 : (Litex.arg __fn_arg 0) ≠ 0 := by
    exact (Exists.choose (Exists.choose_spec (__fn_arg_req)))
  have __wd0_20 : Litex.In 1 Litex.C := by
    exact (Litex.Rules.numeralInC 1)
  have __wd0_21 : Litex.In (Litex.arg __fn_arg 0) Litex.R := by
    exact (Exists.choose (__fn_arg_req))
  have __wd0_22 : Litex.In (Litex.arg __fn_arg 0) Litex.C := by
    exact ((Litex.Rules.realInComplex (Exists.choose (__fn_arg_req))))
  have __obj39_result : Litex.In (Litex.div 1 (Litex.arg __fn_arg 0)) Litex.C := by
    exact ((Litex.Rules.complexDivClosure (__wd0_20) (__wd0_22) (__wd0_19)))
  change Litex.In (Litex.div 1 (Litex.arg __fn_arg 0)) Litex.R
  exact (Litex.Rules.realDivClosure (__wd0_20) (__wd0_22) (__wd0_19) (Litex.Rules.numeralInR 1) (Exists.choose (__fn_arg_req)))

noncomputable def __reciprocal_impl : Litex.Object :=
  Litex.functionObject __reciprocal_spec __reciprocal_body

noncomputable def reciprocal : Litex.Object := __reciprocal_impl

theorem __fact23 : Litex.In reciprocal (Litex.FnSet ({ arity := 1, requirements := fun __fn_arg => ∃ __h_arg0 : Litex.In (Litex.arg __fn_arg 0) Litex.R, ∃ __h_dom0 : (Litex.arg __fn_arg 0) ≠ 0, True, range := fun __fn_arg __fn_arg_len __fn_arg_req => Litex.R } : Litex.FnSpec)) := by
  simpa only [reciprocal, __reciprocal_impl, __reciprocal_spec] using
    (Litex.functionObjectInFnSet __reciprocal_spec __reciprocal_body __reciprocal_closed)

theorem __fact24 : reciprocal = __reciprocal_impl := by
  rfl

theorem __fact34 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) (__h0_2 : a ≠ 0), (reciprocal [a]) = (Litex.div 1 a) :=
by
  intro a __h0_1 __h0_2
  have __wd0_28 : Litex.In a Litex.R := by
    exact (__h0_1)
  have __wd0_29 : a ≠ 0 := by
    exact (__h0_2)
  have __obj50_app : Litex.Applicable (reciprocal) [a] := by
    exact (Litex.fnSetApplicable (args := [a]) __fact23 rfl (by
      change ∃ __h_arg0 : Litex.In (a) Litex.R, ∃ __h_dom0 : (a) ≠ 0, True
      exact Exists.intro (__wd0_28) (Exists.intro (__wd0_29) (True.intro))))
  have __obj50_result : Litex.In (reciprocal [a]) Litex.R := by
    exact (by simpa using (Litex.fnSetResult (args := [a]) __fact23 rfl (by
      change ∃ __h_arg0 : Litex.In (a) Litex.R, ∃ __h_dom0 : (a) ≠ 0, True
      exact Exists.intro (__wd0_28) (Exists.intro (__wd0_29) (True.intro)))))
  have __wd0_30 : a ≠ 0 := by
    exact (__h0_2)
  have __wd0_31 : Litex.In 1 Litex.C := by
    exact (Litex.Rules.numeralInC 1)
  have __wd0_32 : Litex.In a Litex.C := by
    exact ((Litex.Rules.realInComplex (__h0_1)))
  have __obj51_result : Litex.In (Litex.div 1 a) Litex.C := by
    exact ((Litex.Rules.complexDivClosure (__wd0_31) (__wd0_32) (__wd0_30)))
  exact (by
  change ((reciprocal) [a]) = (Litex.div 1 a)
  rw [__fact24]
  unfold __reciprocal_impl
  rw [Litex.functionObject_apply _ _ _ (by
    simpa only [__fact24, __reciprocal_impl] using __obj50_app)]
  simp only [__reciprocal_body, Litex.arg, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil])
```
<!-- END ACTUAL GENERATED LEAN: named_function -->

Lean status: **checked** — generated named-function replay uses the exact local
application certificate with `Litex.functionObject_apply`.

Lean uses `Litex.functionObject`, `functionObjectInFnSet`, and
`functionObject_apply`. Body and range both receive the arity and ordered
requirements proofs. An unavailable defining-equality `FactId`, missing body
occurrence, or missing domain premise fails before Lean emission.

```lean
def id_spec : Litex.FnSpec := ...
def id_body
    (args : List Litex.Object)
    (hLength : args.length = id_spec.arity)
    (hRequirements : id_spec.requirements args) : Litex.Object :=
  Litex.arg args 0
theorem id_closed : ... := by ...
noncomputable def id := Litex.functionObject id_spec id_body
theorem id_in_fn_set : Litex.In id (Litex.FnSet id_spec) := by
  exact Litex.functionObjectInFnSet id_spec id_body id_closed
```

## indexed_aggregate

This entry adds one tuple recipe before generalizing aggregate families.

```litex
have tuple q for i1 <= 2, q[i1] = 0
q = q
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: indexed_aggregate -->
```lean
import Litex.Rules

theorem __q_dim_pos : Litex.In 2 Litex.NPos := by
  exact (Litex.Rules.numeralInNPos 2 (by norm_num))

theorem __q_dim_ge2 : Litex.Le 2 2 := by
  exact (by
  exact (Litex.Rules.numeralLe 2 2).2 (by norm_num))

noncomputable def __q_value (__index1 : Litex.Object) : Litex.Object :=
  0

noncomputable def q : Litex.Object :=
  Litex.tupleObject 2 __q_value __q_dim_pos __q_dim_ge2

theorem __fact6 : Litex.IsTuple q :=
by
  unfold q
  exact Litex.tupleObjectIsTuple 2 __q_value __q_dim_pos __q_dim_ge2

theorem __fact7 : (Litex.tupleDim q) = 2 :=
by
  simpa only [q] using
    (Litex.tupleObject_dim 2 __q_value __q_dim_pos __q_dim_ge2)

theorem __fact14 : ∀ (_binder_2 : Litex.Object) (__h0_1 : Litex.In _binder_2 (Litex.closedRange 1 2)), (Litex.atIndex q _binder_2) = 0 :=
by
  intro __coord __coord_in_range
  simpa only [q, __q_value] using
    (Litex.tupleObject_at 2 __q_value __q_dim_pos __q_dim_ge2 __coord)

theorem __fact15 : q = q := by
  exact rfl
```
<!-- END ACTUAL GENERATED LEAN: indexed_aggregate -->

One `Litex.tupleObject` consumes both dimension checks and exports the exact
is-tuple, dimension, and coordinate effects. Other aggregate families remain
separate until reuse is demonstrated.

```lean
noncomputable def q :=
  Litex.tupleObject 2 q_value q_dimension_positive q_dimension_at_least_two
theorem __fact_<q_is_tuple> : Litex.IsTuple q := Litex.tupleObjectIsTuple ...
```

## statement_object_interactions

This entry contains three deliberate cross-family interactions.

```litex
have fn id(x R) R = x
witness exist x R st {x = 1} from 1:
    1 = 1
obtain y from exist x R st {x = 1}
id(y) = y

thm one_eq_one_by_cases:
    ? forall:
        1 = 1
    by cases:
        ? 1 = 1
        case 1 = 1

have fn into_builder(x R) {z R: z = z} = x
into_builder(1) = 1
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: statement_object_interactions -->
```lean
import Litex.Rules

noncomputable def __litex_id_spec : Litex.FnSpec :=
  ({ arity := 1, requirements := fun __fn_arg => ∃ __h_arg0 : Litex.In (Litex.arg __fn_arg 0) Litex.R, True, range := fun __fn_arg __fn_arg_len __fn_arg_req => Litex.R } : Litex.FnSpec)

noncomputable def __litex_id_body
    (__fn_arg : List Litex.Object)
    (__fn_arg_len : __fn_arg.length = __litex_id_spec.arity)
    (__fn_arg_req : __litex_id_spec.requirements __fn_arg) : Litex.Object :=
  (Litex.arg __fn_arg 0)

theorem __litex_id_closed :
    ∀ __fn_arg __fn_arg_len __fn_arg_req,
      Litex.In
        (__litex_id_body __fn_arg __fn_arg_len __fn_arg_req)
        (__litex_id_spec.range __fn_arg __fn_arg_len __fn_arg_req) := by
  intro __fn_arg __fn_arg_len __fn_arg_req
  change Litex.In (Litex.arg __fn_arg 0) Litex.R
  exact Exists.choose (__fn_arg_req)

noncomputable def __litex_id_impl : Litex.Object :=
  Litex.functionObject __litex_id_spec __litex_id_body

noncomputable def litex_id : Litex.Object := __litex_id_impl

theorem __fact5 : Litex.In litex_id (Litex.FnSet ({ arity := 1, requirements := fun __fn_arg => ∃ __h_arg0 : Litex.In (Litex.arg __fn_arg 0) Litex.R, True, range := fun __fn_arg __fn_arg_len __fn_arg_req => Litex.R } : Litex.FnSpec)) := by
  simpa only [litex_id, __litex_id_impl, __litex_id_spec] using
    (Litex.functionObjectInFnSet __litex_id_spec __litex_id_body __litex_id_closed)

theorem __fact6 : litex_id = __litex_id_impl := by
  rfl

theorem __fact14 : ∃ (x : Litex.Object), Litex.In x Litex.R ∧ x = 1 := by
  exact (by
  have __exist_step1 : (1 : Litex.Object) = 1 := by
    exact rfl
  exact ⟨1, (Litex.Rules.numeralInR 1), (__exist_step1)⟩)

noncomputable def y : Litex.Object := Classical.choose (__fact14)

theorem __fact19 : Litex.In y Litex.R := by
  unfold y
  exact (Classical.choose_spec (__fact14)).1

theorem __fact20 : y = 1 := by
  unfold y
  exact (Classical.choose_spec (__fact14)).2

theorem __fact21 : (litex_id [y]) = y := by
  have __wd0_2 : Litex.In y Litex.R := by
    exact (__fact19)
  have __obj33_app : Litex.Applicable (litex_id) [y] := by
    exact (Litex.fnSetApplicable (args := [y]) __fact5 rfl (by
      change ∃ __h_arg0 : Litex.In (y) Litex.R, True
      exact Exists.intro (__wd0_2) (True.intro)))
  have __obj33_result : Litex.In (litex_id [y]) Litex.R := by
    exact (by simpa using (Litex.fnSetResult (args := [y]) __fact5 rfl (by
      change ∃ __h_arg0 : Litex.In (y) Litex.R, True
      exact Exists.intro (__wd0_2) (True.intro))))
  exact (by
  change ((litex_id) [y]) = y
  rw [__fact6]
  unfold __litex_id_impl
  rw [Litex.functionObject_apply _ _ _ (by
    simpa only [__fact6, __litex_id_impl] using __obj33_app)]
  simp only [__litex_id_body, Litex.arg, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil])

theorem one_eq_one_by_cases : (1 : Litex.Object) = 1 :=
by
  have __step1 : (1 : Litex.Object) = 1 := by
    exact (by
  have __case1 : (1 : Litex.Object) = 1 := rfl
  exact __case1)
  exact rfl

noncomputable def __into_builder_spec : Litex.FnSpec :=
  ({ arity := 1, requirements := fun __fn_arg => ∃ __h_arg0 : Litex.In (Litex.arg __fn_arg 0) Litex.R, True, range := fun __fn_arg __fn_arg_len __fn_arg_req => (Litex.setBuilder Litex.R (fun __x9 => __x9 = __x9)) } : Litex.FnSpec)

noncomputable def __into_builder_body
    (__fn_arg : List Litex.Object)
    (__fn_arg_len : __fn_arg.length = __into_builder_spec.arity)
    (__fn_arg_req : __into_builder_spec.requirements __fn_arg) : Litex.Object :=
  (Litex.arg __fn_arg 0)

theorem __into_builder_closed :
    ∀ __fn_arg __fn_arg_len __fn_arg_req,
      Litex.In
        (__into_builder_body __fn_arg __fn_arg_len __fn_arg_req)
        (__into_builder_spec.range __fn_arg __fn_arg_len __fn_arg_req) := by
  intro __fn_arg __fn_arg_len __fn_arg_req
  change Litex.In (Litex.arg __fn_arg 0) (Litex.setBuilder Litex.R (fun __x9 => __x9 = __x9))
  exact (Litex.inSetBuilder_iff.mpr (And.intro (Exists.choose (__fn_arg_req)) ((rfl))))

noncomputable def __into_builder_impl : Litex.Object :=
  Litex.functionObject __into_builder_spec __into_builder_body

noncomputable def into_builder : Litex.Object := __into_builder_impl

theorem __fact40 : Litex.In into_builder (Litex.FnSet ({ arity := 1, requirements := fun __fn_arg => ∃ __h_arg0 : Litex.In (Litex.arg __fn_arg 0) Litex.R, True, range := fun __fn_arg __fn_arg_len __fn_arg_req => (Litex.setBuilder Litex.R (fun __x9 => __x9 = __x9)) } : Litex.FnSpec)) := by
  simpa only [into_builder, __into_builder_impl, __into_builder_spec] using
    (Litex.functionObjectInFnSet __into_builder_spec __into_builder_body __into_builder_closed)

theorem __fact41 : into_builder = __into_builder_impl := by
  rfl

theorem __fact42 : (into_builder [1]) = 1 := by
  have __wd0_6 : Litex.In 1 Litex.R := by
    exact (Litex.Rules.numeralInR 1)
  have __obj52_app : Litex.Applicable (into_builder) [1] := by
    exact (Litex.fnSetApplicable (args := [1]) __fact40 rfl (by
      change ∃ __h_arg0 : Litex.In (1) Litex.R, True
      exact Exists.intro (__wd0_6) (True.intro)))
  have __obj52_result : Litex.In (into_builder [1]) (Litex.setBuilder Litex.R (fun __x9 => __x9 = __x9)) := by
    exact (by simpa using (Litex.fnSetResult (args := [1]) __fact40 rfl (by
      change ∃ __h_arg0 : Litex.In (1) Litex.R, True
      exact Exists.intro (__wd0_6) (True.intro))))
  exact (by
  change ((into_builder) [1]) = 1
  rw [__fact41]
  unfold __into_builder_impl
  rw [Litex.functionObject_apply _ _ _ (by
    simpa only [__fact41, __into_builder_impl] using __obj52_app)]
  simp only [__into_builder_body, Litex.arg, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil])
```
<!-- END ACTUAL GENERATED LEAN: statement_object_interactions -->

Lean status: **TODO** — the generated statement/function interaction replay
still leaves `Litex.functionObject` application equalities unsolved.

These reuse the basis interfaces; no interaction-specific axiom or escape
hatch is introduced.

The generated file must contain the chosen witness, named-function replay,
the named theorem's local case proof, and `Litex.inSetBuilder_iff.mpr` in one
shared scope.

## anonymous_function

Anonymous functions preserve their own parameter scope, checked return
membership, and application evidence. Alpha-equivalent binders produce equal
function objects, while an applied anonymous head first establishes membership
in the corresponding function set.

```litex
fn(x R) R {x} = fn(y R) R {y}

forall a R:
    fn(x R) R {x}(a) = fn(x R) R {x}(a)
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: anonymous_function -->
```lean
import Litex.Rules

theorem __wd0_3 : ∀ (__wd_scope3_arg1 : Litex.Object) (__wd_scope3_premise1 : Litex.In __wd_scope3_arg1 Litex.R), Litex.In __wd_scope3_arg1 Litex.R :=
by
  intro __wd_scope3_arg1 __wd_scope3_premise1
  exact __wd_scope3_premise1

theorem __wd0_4 : ∀ (__wd_scope4_arg1 : Litex.Object) (__wd_scope4_premise1 : Litex.In __wd_scope4_arg1 Litex.R), Litex.In __wd_scope4_arg1 Litex.R :=
by
  intro __wd_scope4_arg1 __wd_scope4_premise1
  exact __wd_scope4_premise1

noncomputable def __obj7 : Litex.Object :=
  Litex.R

noncomputable def __obj8 (__wd_scope3_arg1 : Litex.Object) : Litex.Object :=
  __wd_scope3_arg1

noncomputable def __obj9_spec : Litex.FnSpec :=
  ({ arity := 1, requirements := fun __arg_0 => ∃ __h_arg0 : Litex.In (Litex.arg __arg_0 0) Litex.R, True, range := fun __arg_0 _ _ => Litex.R } : Litex.FnSpec)

noncomputable def __obj9_body (__obj9_arg : List Litex.Object) (__arg_len : __obj9_arg.length = (__obj9_spec).arity) (__arg_req : (__obj9_spec).requirements __obj9_arg) : Litex.Object :=
  (__obj8 ((Litex.arg __obj9_arg 0)))

theorem __obj9_closed :
    ∀ (__obj9_arg : List Litex.Object)
      (__obj9_arg_len : __obj9_arg.length = (__obj9_spec).arity)
      (__obj9_arg_req : (__obj9_spec).requirements __obj9_arg),
      Litex.In (__obj9_body __obj9_arg __obj9_arg_len __obj9_arg_req) ((__obj9_spec).range __obj9_arg __obj9_arg_len __obj9_arg_req) :=
by
  intro __obj9_arg __obj9_arg_len __obj9_arg_req
  change Litex.In (Litex.arg __obj9_arg 0) Litex.R
  exact (__wd0_3 ((Litex.arg __obj9_arg 0)) (Exists.choose (__obj9_arg_req)))

noncomputable def __obj9 : Litex.Object :=
  Litex.functionObject __obj9_spec __obj9_body

theorem __obj9_in_fn_space :
    Litex.In __obj9 (Litex.FnSet __obj9_spec) := by
  unfold __obj9
  exact Litex.functionObjectInFnSet __obj9_spec __obj9_body __obj9_closed

noncomputable def __obj10 : Litex.Object :=
  Litex.R

noncomputable def __obj11 (__wd_scope4_arg1 : Litex.Object) : Litex.Object :=
  __wd_scope4_arg1

noncomputable def __obj12_spec : Litex.FnSpec :=
  ({ arity := 1, requirements := fun __arg_0 => ∃ __h_arg0 : Litex.In (Litex.arg __arg_0 0) Litex.R, True, range := fun __arg_0 _ _ => Litex.R } : Litex.FnSpec)

noncomputable def __obj12_body (__obj12_arg : List Litex.Object) (__arg_len : __obj12_arg.length = (__obj12_spec).arity) (__arg_req : (__obj12_spec).requirements __obj12_arg) : Litex.Object :=
  (__obj11 ((Litex.arg __obj12_arg 0)))

theorem __obj12_closed :
    ∀ (__obj12_arg : List Litex.Object)
      (__obj12_arg_len : __obj12_arg.length = (__obj12_spec).arity)
      (__obj12_arg_req : (__obj12_spec).requirements __obj12_arg),
      Litex.In (__obj12_body __obj12_arg __obj12_arg_len __obj12_arg_req) ((__obj12_spec).range __obj12_arg __obj12_arg_len __obj12_arg_req) :=
by
  intro __obj12_arg __obj12_arg_len __obj12_arg_req
  change Litex.In (Litex.arg __obj12_arg 0) Litex.R
  exact (__wd0_4 ((Litex.arg __obj12_arg 0)) (Exists.choose (__obj12_arg_req)))

noncomputable def __obj12 : Litex.Object :=
  Litex.functionObject __obj12_spec __obj12_body

theorem __obj12_in_fn_space :
    Litex.In __obj12 (Litex.FnSet __obj12_spec) := by
  unfold __obj12
  exact Litex.functionObjectInFnSet __obj12_spec __obj12_body __obj12_closed

theorem __fact7 : __obj9 = __obj12 := by
  exact rfl

theorem __wd0_11 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) (__wd_scope9_arg1 : Litex.Object) (__wd_scope9_premise1 : Litex.In __wd_scope9_arg1 Litex.R), Litex.In __wd_scope9_arg1 Litex.R :=
by
  intro a __h0_1 __wd_scope9_arg1 __wd_scope9_premise1
  exact __wd_scope9_premise1

theorem __wd0_12 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.R), Litex.In a Litex.R :=
by
  intro a __h0_1
  exact __h0_1

noncomputable def __obj27 : Litex.Object :=
  Litex.R

noncomputable def __obj28 (a : Litex.Object) : Litex.Object :=
  a

noncomputable def __obj29 (__wd_scope9_arg1 : Litex.Object) : Litex.Object :=
  __wd_scope9_arg1

noncomputable def __obj30_spec (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) : Litex.FnSpec :=
  ({ arity := 1, requirements := fun __arg_0 => ∃ __h_arg0 : Litex.In (Litex.arg __arg_0 0) Litex.R, True, range := fun __arg_0 _ _ => Litex.R } : Litex.FnSpec)

noncomputable def __obj30_body (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) (__obj30_arg : List Litex.Object) (__arg_len : __obj30_arg.length = ((__obj30_spec a __h0_1)).arity) (__arg_req : ((__obj30_spec a __h0_1)).requirements __obj30_arg) : Litex.Object :=
  (__obj29 ((Litex.arg __obj30_arg 0)))

theorem __obj30_closed (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) :
    ∀ (__obj30_arg : List Litex.Object)
      (__obj30_arg_len : __obj30_arg.length = ((__obj30_spec a __h0_1)).arity)
      (__obj30_arg_req : ((__obj30_spec a __h0_1)).requirements __obj30_arg),
      Litex.In ((__obj30_body a __h0_1) __obj30_arg __obj30_arg_len __obj30_arg_req) (((__obj30_spec a __h0_1)).range __obj30_arg __obj30_arg_len __obj30_arg_req) :=
by
  intro __obj30_arg __obj30_arg_len __obj30_arg_req
  change Litex.In (Litex.arg __obj30_arg 0) Litex.R
  exact (__wd0_11 (a) (__h0_1) ((Litex.arg __obj30_arg 0)) (Exists.choose (__obj30_arg_req)))

noncomputable def __obj30 (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) : Litex.Object :=
  Litex.functionObject (__obj30_spec a __h0_1) (__obj30_body a __h0_1)

theorem __obj30_in_fn_space (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) :
    Litex.In (__obj30 a __h0_1) (Litex.FnSet (__obj30_spec a __h0_1)) := by
  unfold __obj30
  exact Litex.functionObjectInFnSet (__obj30_spec a __h0_1) (__obj30_body a __h0_1) (__obj30_closed a __h0_1)

theorem __obj31_app : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.R), Litex.Applicable (__obj30 a __h0_1) [(__obj28 a)] :=
by
  intro a __h0_1
  exact Litex.fnSetApplicable (args := [(__obj28 a)]) (__obj30_in_fn_space a __h0_1) rfl (by
  change ∃ __h_arg0 : Litex.In ((__obj28 a)) Litex.R, True
  exact Exists.intro ((__wd0_12 a __h0_1)) (True.intro))

noncomputable def __obj31 (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) : Litex.Object :=
  (__obj30 a __h0_1) [(__obj28 a)]

theorem __obj31_result : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.R), Litex.In (__obj31 a __h0_1) Litex.R :=
by
  intro a __h0_1
  simpa [__obj31] using (Litex.fnSetResult (args := [(__obj28 a)]) (__obj30_in_fn_space a __h0_1) rfl (by
  change ∃ __h_arg0 : Litex.In ((__obj28 a)) Litex.R, True
  exact Exists.intro ((__wd0_12 a __h0_1)) (True.intro)))

theorem __wd0_13 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) (__wd_scope10_arg1 : Litex.Object) (__wd_scope10_premise1 : Litex.In __wd_scope10_arg1 Litex.R), Litex.In __wd_scope10_arg1 Litex.R :=
by
  intro a __h0_1 __wd_scope10_arg1 __wd_scope10_premise1
  exact __wd_scope10_premise1

theorem __wd0_14 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.R), Litex.In a Litex.R :=
by
  intro a __h0_1
  exact __h0_1

noncomputable def __obj32 (__wd_scope10_arg1 : Litex.Object) : Litex.Object :=
  __wd_scope10_arg1

noncomputable def __obj33_spec (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) : Litex.FnSpec :=
  ({ arity := 1, requirements := fun __arg_0 => ∃ __h_arg0 : Litex.In (Litex.arg __arg_0 0) Litex.R, True, range := fun __arg_0 _ _ => Litex.R } : Litex.FnSpec)

noncomputable def __obj33_body (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) (__obj33_arg : List Litex.Object) (__arg_len : __obj33_arg.length = ((__obj33_spec a __h0_1)).arity) (__arg_req : ((__obj33_spec a __h0_1)).requirements __obj33_arg) : Litex.Object :=
  (__obj32 ((Litex.arg __obj33_arg 0)))

theorem __obj33_closed (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) :
    ∀ (__obj33_arg : List Litex.Object)
      (__obj33_arg_len : __obj33_arg.length = ((__obj33_spec a __h0_1)).arity)
      (__obj33_arg_req : ((__obj33_spec a __h0_1)).requirements __obj33_arg),
      Litex.In ((__obj33_body a __h0_1) __obj33_arg __obj33_arg_len __obj33_arg_req) (((__obj33_spec a __h0_1)).range __obj33_arg __obj33_arg_len __obj33_arg_req) :=
by
  intro __obj33_arg __obj33_arg_len __obj33_arg_req
  change Litex.In (Litex.arg __obj33_arg 0) Litex.R
  exact (__wd0_13 (a) (__h0_1) ((Litex.arg __obj33_arg 0)) (Exists.choose (__obj33_arg_req)))

noncomputable def __obj33 (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) : Litex.Object :=
  Litex.functionObject (__obj33_spec a __h0_1) (__obj33_body a __h0_1)

theorem __obj33_in_fn_space (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) :
    Litex.In (__obj33 a __h0_1) (Litex.FnSet (__obj33_spec a __h0_1)) := by
  unfold __obj33
  exact Litex.functionObjectInFnSet (__obj33_spec a __h0_1) (__obj33_body a __h0_1) (__obj33_closed a __h0_1)

theorem __obj34_app : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.R), Litex.Applicable (__obj33 a __h0_1) [(__obj28 a)] :=
by
  intro a __h0_1
  exact Litex.fnSetApplicable (args := [(__obj28 a)]) (__obj33_in_fn_space a __h0_1) rfl (by
  change ∃ __h_arg0 : Litex.In ((__obj28 a)) Litex.R, True
  exact Exists.intro ((__wd0_14 a __h0_1)) (True.intro))

noncomputable def __obj34 (a : Litex.Object) (__h0_1 : Litex.In a Litex.R) : Litex.Object :=
  (__obj33 a __h0_1) [(__obj28 a)]

theorem __obj34_result : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.R), Litex.In (__obj34 a __h0_1) Litex.R :=
by
  intro a __h0_1
  simpa [__obj34] using (Litex.fnSetResult (args := [(__obj28 a)]) (__obj33_in_fn_space a __h0_1) rfl (by
  change ∃ __h_arg0 : Litex.In ((__obj28 a)) Litex.R, True
  exact Exists.intro ((__wd0_14 a __h0_1)) (True.intro)))

theorem __fact20 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.R), (__obj31 a __h0_1) = (__obj34 a __h0_1) :=
by
  intro a __h0_1
  exact rfl
```
<!-- END ACTUAL GENERATED LEAN: anonymous_function -->

Required generated shape:

```lean
noncomputable def anonymous_fn_<id> : Litex.Object :=
  Litex.functionObject anonymous_fn_<id>_spec anonymous_fn_<id>_body

theorem anonymous_fn_<id>_applicable :
    Litex.Applicable anonymous_fn_<id> [a] := by ...
```

Boundary: `fn(x R) N {x}` remains rejected because the body has no proof that
an arbitrary real parameter belongs to `N`. Compound anonymous bodies such as
`fn(x R) R {x + 1}` remain a fail-closed emitter-scope boundary until their
binder-owned WD DAG is replayed inside the closure proof instead of through
generalized top-level helpers.

## arithmetic_forall_wd

Nested universal facts, subtraction, and function applications retain the
well-definedness evidence selected for each source occurrence. The object `y`
stays in the universal object type. Its real membership is replayed in a local
parameterized WD bundle; subtraction and application terms remain proof-free.

```litex
forall f fn(x R) R:
    forall y R:
        f(y) = f(y - 1)
    =>:
        f(2) = f(1)
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: arithmetic_forall_wd -->
```lean
import Litex.Rules

theorem __fact22 : ∀ (f : Litex.Object) (__h0_1 : Litex.In f (Litex.fnSpace1 Litex.R Litex.R)) (__h0_2 : ∀ (y : Litex.Object) (__h1_1 : Litex.In y Litex.R), (f [y]) = (f [(Litex.sub y 1)])), (f [2]) = (f [1]) :=
by
  intro f __h0_1 __h0_2
  have __scope0 : ∀ (y : Litex.Object) (__h1_1 : Litex.In y Litex.R), Litex.In y Litex.R ∧ (Litex.Applicable (f) [y] ∧ (Litex.In (f [y]) Litex.R)) := by
    exact (by
      intro y __h1_1
      have __wd1_8 : Litex.In y Litex.R := by
        exact (__h1_1)
      have __obj29_app : Litex.Applicable (f) [y] := by
        exact (Litex.fnSpaceApplicable (args := [y]) __h0_1 rfl (by
          change ∃ __h_arg0 : Litex.In (y) Litex.R, True
          exact Exists.intro (__wd1_8) (True.intro)))
      have __obj29_result : Litex.In (f [y]) Litex.R := by
        exact (by simpa using (Litex.fnSpaceResult (args := [y]) __h0_1 rfl (by
          change ∃ __h_arg0 : Litex.In (y) Litex.R, True
          exact Exists.intro (__wd1_8) (True.intro))))
      exact And.intro (__wd1_8) (And.intro (__obj29_app) ((__obj29_result))))
  have __scope1 : ∀ (y : Litex.Object) (__h1_1 : Litex.In y Litex.R), Litex.In y Litex.C ∧ (Litex.In 1 Litex.C ∧ (Litex.In 1 Litex.R ∧ (Litex.In (Litex.sub y 1) Litex.R ∧ (Litex.In (Litex.sub y 1) Litex.C ∧ (Litex.Applicable (f) [(Litex.sub y 1)] ∧ (Litex.In (f [(Litex.sub y 1)]) Litex.R)))))) := by
    exact (by
      intro y __h1_1
      have __wd1_9 : Litex.In y Litex.C := by
        exact ((Litex.Rules.realInComplex (__h1_1)))
      have __wd1_10 : Litex.In 1 Litex.C := by
        exact (Litex.Rules.numeralInC 1)
      have __wd1_11 : Litex.In 1 Litex.R := by
        exact (Litex.Rules.numeralInR 1)
      have __wd1_12 : Litex.In (Litex.sub y 1) Litex.R := by
        exact ((Litex.Rules.realSubClosure (__wd1_9) (__wd1_10) (__h1_1) (Litex.Rules.numeralInR 1)))
      have __obj32_result : Litex.In (Litex.sub y 1) Litex.C := by
        exact ((Litex.Rules.complexSubClosure (__wd1_9) (__wd1_10)))
      have __obj33_app : Litex.Applicable (f) [(Litex.sub y 1)] := by
        exact (Litex.fnSpaceApplicable (args := [(Litex.sub y 1)]) __h0_1 rfl (by
          change ∃ __h_arg0 : Litex.In ((Litex.sub y 1)) Litex.R, True
          exact Exists.intro (__wd1_12) (True.intro)))
      have __obj33_result : Litex.In (f [(Litex.sub y 1)]) Litex.R := by
        exact (by simpa using (Litex.fnSpaceResult (args := [(Litex.sub y 1)]) __h0_1 rfl (by
          change ∃ __h_arg0 : Litex.In ((Litex.sub y 1)) Litex.R, True
          exact Exists.intro (__wd1_12) (True.intro))))
      exact And.intro (__wd1_9) (And.intro (__wd1_10) (And.intro (__wd1_11) (And.intro (__wd1_12) (And.intro (__obj32_result) (And.intro (__obj33_app) ((__obj33_result))))))))
  have __wd0_13 : Litex.In 2 Litex.R := by
    exact (Litex.Rules.numeralInR 2)
  have __obj36_app : Litex.Applicable (f) [2] := by
    exact (Litex.fnSpaceApplicable (args := [2]) __h0_1 rfl (by
      change ∃ __h_arg0 : Litex.In (2) Litex.R, True
      exact Exists.intro (__wd0_13) (True.intro)))
  have __obj36_result : Litex.In (f [2]) Litex.R := by
    exact (by simpa using (Litex.fnSpaceResult (args := [2]) __h0_1 rfl (by
      change ∃ __h_arg0 : Litex.In (2) Litex.R, True
      exact Exists.intro (__wd0_13) (True.intro))))
  have __wd0_14 : Litex.In 1 Litex.R := by
    exact (Litex.Rules.numeralInR 1)
  have __obj38_app : Litex.Applicable (f) [1] := by
    exact (Litex.fnSpaceApplicable (args := [1]) __h0_1 rfl (by
      change ∃ __h_arg0 : Litex.In (1) Litex.R, True
      exact Exists.intro (__wd0_14) (True.intro)))
  have __obj38_result : Litex.In (f [1]) Litex.R := by
    exact (by simpa using (Litex.fnSpaceResult (args := [1]) __h0_1 rfl (by
      change ∃ __h_arg0 : Litex.In (1) Litex.R, True
      exact Exists.intro (__wd0_14) (True.intro))))
  exact (by
  have __normalized := ((__h0_2 (Litex.add 1 1) ((Litex.Rules.realAddClosure ((Litex.Rules.numeralInC 1)) ((Litex.Rules.numeralInC 1)) (Litex.Rules.numeralInR 1) (Litex.Rules.numeralInR 1)))))
  simp only [OfNat.ofNat, Litex.add_embedComplex, Litex.sub_embedComplex, Litex.mul_embedComplex, Litex.div_embedComplex] at __normalized ⊢
  norm_num at __normalized ⊢
  exact __normalized)
```
<!-- END ACTUAL GENERATED LEAN: arithmetic_forall_wd -->

Required generated shape:

```lean
theorem __fact_<forall> : ∀ (f : Litex.Object), ... := by
  intro f __h0_1 __h0_2
  have __scope... : ∀ y __h1_1, ... := by
    intro y __h1_1
    have __wd1_<sub> : Litex.In (Litex.sub y 1) Litex.R := by
      exact Litex.Rules.realSubClosure ...
    ...
  ...
```

Boundary: missing or retargeted occurrence evidence fails emission; the
compiler does not recover it from rendered object text.

## first_statement_tranche

This group combines an abstract predicate, a defined predicate, a concrete
predicate fact, an object definition, definition folding, and explicit trust.
Only the explicitly trusted source proposition becomes a Lean axiom.

```litex
abstract_prop marked(x)

prop is_zero(x R):
    x = 0

$is_zero(0)

have named_zero R = 0
by def $is_zero(named_zero)

trust $marked(named_zero)
$marked(named_zero)
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: first_statement_tranche -->
```lean
import Litex.Rules

axiom marked : Litex.Object → Prop

def is_zero (x : Litex.Object) : Prop :=
  Litex.In x Litex.R ∧ (x = 0)

theorem __fact3 : is_zero 0 := by
  exact (by
  change Litex.In 0 Litex.R ∧ ((0 : Litex.Object) = 0)
  exact And.intro (Litex.Rules.numeralInR 0) ((rfl)))

theorem __fact4 : Litex.In 0 Litex.R := by
  exact (by
  have __definition := (__fact3)
  change Litex.In 0 Litex.R ∧ ((0 : Litex.Object) = 0) at __definition
  exact (__definition).1)

theorem __fact5 : (0 : Litex.Object) = 0 := by
  exact (by
  have __definition := (__fact3)
  change Litex.In 0 Litex.R ∧ ((0 : Litex.Object) = 0) at __definition
  exact (__definition).2)

noncomputable def named_zero : Litex.Object := 0

theorem __fact7 : Litex.In named_zero Litex.R := by
  simpa only [named_zero] using (__fact4)

theorem __fact8 : named_zero = 0 := by
  rfl

theorem __fact9 : is_zero named_zero := by
  exact (by
  change Litex.In named_zero Litex.R ∧ (named_zero = 0)
  exact And.intro (__fact7) ((__fact8)))

axiom __fact10 : marked named_zero
```
<!-- END ACTUAL GENERATED LEAN: first_statement_tranche -->

Required generated shape:

```lean
axiom marked : Litex.Object → Prop
def is_zero (x : Litex.Object) : Prop := Litex.In x Litex.R ∧ x = 0
noncomputable def named_zero : Litex.Object := 0
axiom __fact_<trusted> : marked named_zero
```

Boundary: bodyless concrete predicates and `trust have` remain unsupported;
unsupported declarations do not produce implicit target axioms.

## known_equality_path

Known equality symmetry and transitivity cite the exact stored equality facts.
The emitted proof uses those identities directly instead of searching for a
path between proposition texts.

```litex
forall a, b set:
    a = b
    =>:
        b = a

forall a, b, c set:
    a = b
    b = c
    =>:
        a = c
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: known_equality_path -->
```lean
import Litex.Rules

theorem __fact13 : ∀ (a : Litex.Object) (__h0_1 : Litex.IsSet a) (b : Litex.Object) (__h0_2 : Litex.IsSet b) (__h0_3 : a = b), b = a :=
by
  intro a __h0_1 b __h0_2 __h0_3
  exact (Eq.symm (__h0_3))

theorem __fact32 : ∀ (a : Litex.Object) (__h0_1 : Litex.IsSet a) (b : Litex.Object) (__h0_2 : Litex.IsSet b) (c : Litex.Object) (__h0_3 : Litex.IsSet c) (__h0_4 : a = b) (__h0_5 : b = c), a = c :=
by
  intro a __h0_1 b __h0_2 c __h0_3 __h0_4 __h0_5
  exact (Eq.trans ((__h0_4)) ((__h0_5)))
```
<!-- END ACTUAL GENERATED LEAN: known_equality_path -->

Required generated shape:

```lean
theorem __fact_<symm> ... : b = a := by
  exact Eq.symm __fact<a_eq_b>

theorem __fact_<trans> ... : a = c := by
  exact Eq.trans __fact<a_eq_b> __fact<b_eq_c>
```

Boundary: an unavailable, disconnected, or out-of-scope equality fact is
rejected rather than replaced by target-side equality search.

## litex_object_abi

Every source object lowers to `Litex.Object`. Membership in `C` and `R` is
retained as independent evidence, so proving `a ∈ R` enables the same object
`a` to be passed to an `R`-domain function without a cast or retyping step.

```litex
forall a C, f fn(x R) R:
    a = 1
    =>:
        1 $in R
        a $in R
        f(a) = f(a)
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: litex_object_abi -->
```lean
import Litex.Rules

theorem __fact27 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.C) (__h0_2 : a = 1), Litex.In 1 Litex.R :=
by
  intro a __h0_1 __h0_2
  exact Litex.Rules.numeralInR 1

theorem __fact28 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.C) (__h0_2 : a = 1), Litex.In a Litex.R :=
by
  intro a __h0_1 __h0_2
  exact by simpa only [__h0_2] using (__fact27 a __h0_1 __h0_2)

theorem __fact26 : ∀ (a : Litex.Object) (__h0_1 : Litex.In a Litex.C) (f : Litex.Object) (__h0_2 : Litex.In f (Litex.fnSpace1 Litex.R Litex.R)) (__h0_3 : a = 1), (f [a]) = (f [a]) :=
by
  intro a __h0_1 f __h0_2 __h0_3
  have __wd0_2 : Litex.In a Litex.R := by
    exact (by simpa only [__h0_3] using (__fact27 a __h0_1 __h0_3))
  have __wd0_3 : Litex.In a Litex.R := by
    exact (__fact28 a __h0_1 __h0_3)
  have __obj24_app : Litex.Applicable (f) [a] := by
    exact (Litex.fnSpaceApplicable (args := [a]) __h0_2 rfl (by
      change ∃ __h_arg0 : Litex.In (a) Litex.R, True
      exact Exists.intro (__wd0_3) (True.intro)))
  have __obj24_result : Litex.In (f [a]) Litex.R := by
    exact (by simpa using (Litex.fnSpaceResult (args := [a]) __h0_2 rfl (by
      change ∃ __h_arg0 : Litex.In (a) Litex.R, True
      exact Exists.intro (__wd0_3) (True.intro))))
  exact rfl
```
<!-- END ACTUAL GENERATED LEAN: litex_object_abi -->

Required generated shape:

```lean
theorem __fact_<forall> :
    ∀ (a : Litex.Object) (_ : Litex.In a Litex.C)
      (f : Litex.Object) (_ : Litex.In f (Litex.fnSpace1 Litex.R Litex.R)),
      a = 1 → Litex.In 1 Litex.R → Litex.In a Litex.R → ... := by ...
```

Boundary: without a proof of `a $in R`, `f(a)` remains rejected even though
both values have Lean type `Litex.Object`.

## set_predicate_definitions

Nonempty-set and finite-set parameters use predicates derived from membership
and sethood rather than independent opaque target axioms.

```litex
forall s nonempty_set, t finite_set:
    s = s
    t = t
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: set_predicate_definitions -->
```lean
import Litex.Rules

theorem __fact13 : ∀ (s : Litex.Object) (__h0_1 : Litex.IsNonemptySet s), s = s :=
by
  intro s __h0_1
  exact rfl

theorem __fact14 : ∀ (t : Litex.Object) (__h0_1 : Litex.IsFiniteSet t), t = t :=
by
  intro t __h0_1
  exact rfl
```
<!-- END ACTUAL GENERATED LEAN: set_predicate_definitions -->

Required generated shape:

```lean
theorem __fact_<forall> :
    ∀ (s : Litex.Object) (_ : Litex.IsNonemptySet s)
      (t : Litex.Object) (_ : Litex.IsFiniteSet t),
      s = s ∧ t = t := by ...
```

Boundary: finiteness does not imply nonemptiness, and a finite extension alone
does not create a separate source object or carrier type.

## shared_builtin_rules

Generated files import the shared checked builtin-rule library. Concrete
not-equality symmetry and numeral-membership facts call those theorems instead
of copying theorem bodies or introducing new axioms.

```litex
forall a, b set:
    a != b
    =>:
        b != a

1 $in N
1 $in C
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: shared_builtin_rules -->
```lean
import Litex.Rules

theorem __fact13 : ∀ (a : Litex.Object) (__h0_1 : Litex.IsSet a) (b : Litex.Object) (__h0_2 : Litex.IsSet b) (__h0_3 : a ≠ b), b ≠ a :=
by
  intro a __h0_1 b __h0_2 __h0_3
  exact (Litex.Rules.notEqualSymmetry (__h0_3))

theorem __fact14 : Litex.In 1 Litex.N := by
  exact Litex.Rules.numeralInN 1

theorem __fact15 : Litex.Le 0 1 := by
  exact (by
  exact (Litex.Rules.numeralLe 0 1).2 (by norm_num))

theorem __fact17 : Litex.In 1 Litex.C := by
  exact Litex.Rules.numeralInC 1
```
<!-- END ACTUAL GENERATED LEAN: shared_builtin_rules -->

Required generated shape:

```lean
import Litex.Rules

exact Litex.Rules.notEqualSymmetry __fact<a_ne_b>
exact Litex.Rules.numeralInN 1
exact Litex.Rules.numeralInC 1
```

Boundary: a verifier builtin without a checked shared-theorem adapter remains
unsupported; the compiler does not generate an inline proof or axiom fallback.

## resolved_builtin_computation

Checked object definitions may be unfolded to expose a closed atomic fact to
Litex's ordinary builtin computation. The verifier keeps the computed fact as
an explicit premise (`2 $in Z` here), freezes the defining equalities by
`FactId`, and records normalization plus equality-rewrite steps back to the
original source proposition.

```litex
have one Z = 1
have integer_set set = Z

one + 1 $in integer_set
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: resolved_builtin_computation -->
```lean
import Litex.Rules

noncomputable def one : Litex.Object := 1

theorem __fact2 : Litex.In one Litex.Z := by
  simpa only [one] using (Litex.Rules.numeralInZ 1)

theorem __fact3 : one = 1 := by
  rfl

noncomputable def integer_set : Litex.Object := Litex.Z

theorem __fact5 : Litex.IsSet integer_set := by
  simpa only [integer_set] using (Litex.Rules.objectIsSet Litex.Z)

theorem __fact6 : integer_set = Litex.Z := by
  rfl

theorem __fact7 : Litex.In (Litex.add one 1) integer_set := by
  have __wd0_1 : Litex.In one Litex.C := by
    exact (by simpa only [__fact3] using (Litex.Rules.numeralInC 1))
  have __wd0_2 : Litex.In 1 Litex.C := by
    exact (Litex.Rules.numeralInC 1)
  have __obj9_result : Litex.In (Litex.add one 1) Litex.C := by
    exact ((Litex.Rules.complexAddClosure (__wd0_1) (__wd0_2)))
  exact by simpa only [__fact6, __fact3] using ((by
  have __normalized := (Litex.Rules.numeralInZ 2)
  simp only [OfNat.ofNat, Litex.add_embedComplex, Litex.sub_embedComplex, Litex.mul_embedComplex, Litex.div_embedComplex] at __normalized ⊢
  norm_num at __normalized ⊢
  exact __normalized))

theorem __fact8 : Litex.In (Litex.add one 1) Litex.Z := by
  have __wd0_1 : Litex.In one Litex.C := by
    exact (by simpa only [__fact3] using (Litex.Rules.numeralInC 1))
  have __wd0_2 : Litex.In 1 Litex.C := by
    exact (Litex.Rules.numeralInC 1)
  have __obj9_result : Litex.In (Litex.add one 1) Litex.C := by
    exact ((Litex.Rules.complexAddClosure (__wd0_1) (__wd0_2)))
  exact by simpa only [__fact6] using (__fact7)
```
<!-- END ACTUAL GENERATED LEAN: resolved_builtin_computation -->

Required generated shape:

```lean
noncomputable def one : Litex.Object := 1
noncomputable def integer_set : Litex.Object := Litex.Z

theorem __fact_<resolved> : Litex.In (Litex.add one 1) integer_set := by
  simpa only [__fact<one_eq_one>, __fact<integer_set_eq_Z>] using
    <normalization of the closed proof of Litex.In 2 Litex.Z>
```

Boundary: a bodyless `have unknown_set set` has no defining equality, so
`one + 1 $in unknown_set` remains unknown. Ordinary proved equalities are not
silently reclassified as object definitions, and missing equality `FactId`
provenance fails Lean IR construction.

## example_and_sketch

`example` checks one explicit goal in a disposable scope and maps to Lean's
anonymous `example` declaration. `sketch` has no target; its checked statements
are replayed in source order inside an isolated generated namespace. Neither
statement exports its local facts into the following Litex context.

```litex
example:
    ? 1 = 1
    2 = 2

example:
    ? forall x R:
        x = x

sketch:
    3 = 3
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: example_and_sketch -->
```lean
import Litex.Rules

example : (1 : Litex.Object) = 1 :=
by
  have __step_1 : (2 : Litex.Object) = 2 := by
    exact (rfl)
  exact rfl

example : ∀ (x : Litex.Object) (__h0_1 : Litex.In x Litex.R), x = x :=
by
  intro x __h0_1
  exact rfl

namespace __Sketch01

theorem __fact5 : (3 : Litex.Object) = 3 := by
  exact rfl

end __Sketch01
```
<!-- END ACTUAL GENERATED LEAN: example_and_sketch -->

Required generated shape:

```lean
example : <checked proposition> := by
  <local checked proof steps>
  exact <checked target proof>

namespace __Sketch<index>
  <ordinary checked declarations for the sketch statements>
end __Sketch<index>
```

Boundary: `example` and `sketch` have no exported `FactId` in the surrounding
Litex environment. An explicit `trust` inside a sketch remains an explicit
namespaced Lean axiom; unsupported statements fail closed and never become
`sorry` or compiler-invented axioms.
