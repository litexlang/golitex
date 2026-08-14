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

theorem fact43 : ∀ (a : Litex.Object) (h_0_1 : Litex.In a Litex.R) (b : Litex.Object) (h_0_2 : Litex.In b Litex.R) (g : Litex.Object) (h_0_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (h_0_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (h_0_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, ∃ litex_requirement_2 : Litex.In (Litex.arg litex_args_0 1) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))), (f [(g [a]), (t [b])]) = (f [(g [a]), (t [b])]) :=
by
  intro a h_0_1 b h_0_2 g h_0_3 t h_0_4 f h_0_5
  have wd_0_7 : Litex.In a Litex.R := by
    exact (h_0_1)
  have obj_44_applicable : Litex.Applicable (g) [a] := by
    exact (Litex.fnSetApplicable h_0_3 rfl (by
      change ∃ litex_application_requirement_1 : Litex.In (a) Litex.R, True
      exact Exists.intro (wd_0_7) (True.intro)))
  have obj_44_result : Litex.In (g [a]) Litex.R := by
    exact (by simpa using (Litex.fnSetResult h_0_3 rfl (by
      change ∃ litex_application_requirement_1 : Litex.In (a) Litex.R, True
      exact Exists.intro (wd_0_7) (True.intro))))
  have wd_0_8 : Litex.In b Litex.R := by
    exact (h_0_2)
  have obj_45_applicable : Litex.Applicable (t) [b] := by
    exact (Litex.fnSetApplicable h_0_4 rfl (by
      change ∃ litex_application_requirement_1 : Litex.In (b) Litex.R, True
      exact Exists.intro (wd_0_8) (True.intro)))
  have obj_45_result : Litex.In (t [b]) Litex.R := by
    exact (by simpa using (Litex.fnSetResult h_0_4 rfl (by
      change ∃ litex_application_requirement_1 : Litex.In (b) Litex.R, True
      exact Exists.intro (wd_0_8) (True.intro))))
  have wd_0_9 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec)) := by
    exact (h_0_3)
  have wd_0_10 : Litex.In (g [a]) Litex.R := by
    exact ((by simpa using (Litex.fnSetResult h_0_3 rfl (by
      change ∃ litex_application_requirement_1 : Litex.In (a) Litex.R, True
      exact Exists.intro (wd_0_7) (True.intro)))))
  have wd_0_11 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec)) := by
    exact (h_0_4)
  have wd_0_12 : Litex.In (t [b]) Litex.R := by
    exact ((by simpa using (Litex.fnSetResult h_0_4 rfl (by
      change ∃ litex_application_requirement_1 : Litex.In (b) Litex.R, True
      exact Exists.intro (wd_0_8) (True.intro)))))
  have obj_46_applicable : Litex.Applicable (f) [(g [a]), (t [b])] := by
    exact (Litex.fnSetApplicable h_0_5 rfl (by
      change ∃ litex_application_requirement_1 : Litex.In ((g [a])) Litex.R, ∃ litex_application_requirement_2 : Litex.In ((t [b])) Litex.R, True
      exact Exists.intro (wd_0_10) (Exists.intro (wd_0_12) (True.intro))))
  have obj_46_result : Litex.In (f [(g [a]), (t [b])]) Litex.R := by
    exact (by simpa using (Litex.fnSetResult h_0_5 rfl (by
      change ∃ litex_application_requirement_1 : Litex.In ((g [a])) Litex.R, ∃ litex_application_requirement_2 : Litex.In ((t [b])) Litex.R, True
      exact Exists.intro (wd_0_10) (Exists.intro (wd_0_12) (True.intro)))))
  exact rfl
```
<!-- END ACTUAL GENERATED LEAN: well_defined_object_dag -->

Required generated shape:

```lean
theorem fact... : f [g [a], t [b]] = f [g [a], t [b]] := by
  intro a h_a b h_b g h_g t h_t f h_f
  have obj_<g>_applicable : Litex.Applicable g [a] := ...
  have obj_<g>_result : Litex.In (g [a]) Litex.R := ...
  have obj_<t>_applicable : Litex.Applicable t [b] := ...
  have obj_<t>_result : Litex.In (t [b]) Litex.R := ...
  have obj_<outer>_applicable : Litex.Applicable f [g [a], t [b]] := ...
  exact rfl
```

Each selected `WellDefinedObjId` owns stable local applicability/result names,
and verifier propositions remain separately named by
`wd_<environment-depth>_<WellDefinedFactId>`. The emitter follows the retained
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

axiom fact3 : ∀ (x : Litex.Object) (h_0_1 : Litex.In x Litex.R), p x

theorem fact4 : p 1 := by
  exact (fact3 1 (Litex.Rules.numeralInR 1))
```
<!-- END ACTUAL GENERATED LEAN: trusted_forall_atomic_fact -->

Required generated shape:

```lean
axiom p : Litex.Object → Prop
axiom fact... :
  ∀ (x : Litex.Object) (_ : Litex.In x Litex.R), p x

theorem fact... : p 1 := by
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

theorem fact13 : ∀ (a : Litex.Object) (h_0_1 : Litex.In a Litex.C) (b : Litex.Object) (h_0_2 : Litex.In b Litex.C) (c : Litex.Object) (h_0_3 : Litex.In c Litex.C), (Litex.add (Litex.add a b) c) = (Litex.add (Litex.add a b) c) :=
by
  intro a h_0_1 b h_0_2 c h_0_3
  have wd_0_5 : Litex.In a Litex.C := by
    exact (h_0_1)
  have wd_0_6 : Litex.In b Litex.C := by
    exact (h_0_2)
  have wd_0_7 : Litex.In (Litex.add a b) Litex.C := by
    exact ((Litex.Rules.complexAddClosure (wd_0_5) (wd_0_6)))
  have wd_0_8 : Litex.In c Litex.C := by
    exact (h_0_3)
  have obj_12_result : Litex.In (Litex.add (Litex.add a b) c) Litex.C := by
    exact ((Litex.Rules.complexAddClosure (wd_0_7) (wd_0_8)))
  exact rfl

theorem fact26 : ∀ (a : Litex.Object) (h_0_1 : Litex.In a Litex.C) (b : Litex.Object) (h_0_2 : Litex.In b Litex.C) (c : Litex.Object) (h_0_3 : Litex.In c Litex.C), (Litex.add (Litex.mul (Litex.sub a b) c) a) = (Litex.add (Litex.mul (Litex.sub a b) c) a) :=
by
  intro a h_0_1 b h_0_2 c h_0_3
  have wd_0_19 : Litex.In a Litex.C := by
    exact (h_0_1)
  have wd_0_20 : Litex.In b Litex.C := by
    exact (h_0_2)
  have wd_0_21 : Litex.In (Litex.sub a b) Litex.C := by
    exact ((Litex.Rules.complexSubClosure (wd_0_19) (wd_0_20)))
  have wd_0_22 : Litex.In c Litex.C := by
    exact (h_0_3)
  have wd_0_23 : Litex.In (Litex.mul (Litex.sub a b) c) Litex.C := by
    exact ((Litex.Rules.complexMulClosure (wd_0_21) (wd_0_22)))
  have wd_0_24 : Litex.In a Litex.C := by
    exact (h_0_1)
  have obj_32_result : Litex.In (Litex.add (Litex.mul (Litex.sub a b) c) a) Litex.C := by
    exact ((Litex.Rules.complexAddClosure (wd_0_23) (wd_0_24)))
  exact rfl

theorem fact39 : ∀ (a : Litex.Object) (h_0_1 : Litex.In a Litex.C) (b : Litex.Object) (h_0_2 : Litex.In b Litex.C) (h_0_3 : b ≠ 0), (Litex.div a b) = (Litex.div a b) :=
by
  intro a h_0_1 b h_0_2 h_0_3
  have wd_0_34 : b ≠ 0 := by
    exact (h_0_3)
  have wd_0_35 : Litex.In a Litex.C := by
    exact (h_0_1)
  have wd_0_36 : Litex.In b Litex.C := by
    exact (h_0_2)
  have obj_49_result : Litex.In (Litex.div a b) Litex.C := by
    exact ((Litex.Rules.complexDivClosure (wd_0_35) (wd_0_36) (wd_0_34)))
  exact rfl

theorem fact52 : ∀ (a : Litex.Object) (h_0_1 : Litex.In a Litex.C) (b : Litex.Object) (h_0_2 : Litex.In b Litex.C) (h_0_3 : b ≠ 0), (Litex.add (Litex.div a b) a) = (Litex.add (Litex.div a b) a) :=
by
  intro a h_0_1 b h_0_2 h_0_3
  have wd_0_45 : b ≠ 0 := by
    exact (h_0_3)
  have wd_0_46 : Litex.In a Litex.C := by
    exact (h_0_1)
  have wd_0_47 : Litex.In b Litex.C := by
    exact (h_0_2)
  have wd_0_48 : Litex.In (Litex.div a b) Litex.C := by
    exact ((Litex.Rules.complexDivClosure (wd_0_46) (wd_0_47) (wd_0_45)))
  have wd_0_49 : Litex.In a Litex.C := by
    exact (h_0_1)
  have obj_66_result : Litex.In (Litex.add (Litex.div a b) a) Litex.C := by
    exact ((Litex.Rules.complexAddClosure (wd_0_48) (wd_0_49)))
  exact rfl

theorem fact65 : ∀ (a : Litex.Object) (h_0_1 : Litex.In a Litex.R) (b : Litex.Object) (h_0_2 : Litex.In b Litex.R) (h_0_3 : b ≠ 0), Litex.In (Litex.div a b) Litex.R :=
by
  intro a h_0_1 b h_0_2 h_0_3
  have wd_0_60 : b ≠ 0 := by
    exact (h_0_3)
  have wd_0_61 : Litex.In a Litex.R := by
    exact (h_0_1)
  have wd_0_62 : Litex.In a Litex.C := by
    exact ((Litex.Rules.realInComplex (h_0_1)))
  have wd_0_63 : Litex.In b Litex.R := by
    exact (h_0_2)
  have wd_0_64 : Litex.In b Litex.C := by
    exact ((Litex.Rules.realInComplex (h_0_2)))
  have obj_84_result : Litex.In (Litex.div a b) Litex.C := by
    exact ((Litex.Rules.complexDivClosure (wd_0_62) (wd_0_64) (wd_0_60)))
  exact (Litex.Rules.realDivClosure (wd_0_62) (wd_0_64) (wd_0_60) (h_0_1) (h_0_2))
```
<!-- END ACTUAL GENERATED LEAN: proof_carrying_arithmetic -->

Required generated shape:

```lean
theorem fact... : Litex.add (Litex.div a b) a =
    Litex.add (Litex.div a b) a := by
  intro a h_a b h_b h_nonzero
  have wd_0_<a_in_C> : Litex.In a Litex.C := by exact h_a
  have wd_0_<b_in_C> : Litex.In b Litex.C := by exact h_b
  have wd_0_<b_ne_zero> : b ≠ 0 := by exact h_nonzero
  have wd_0_<quotient_in_C> : Litex.In (Litex.div a b) Litex.C := by
    exact Litex.Rules.complexDivClosure
      wd_0_<a_in_C> wd_0_<b_in_C> wd_0_<b_ne_zero>
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

theorem fact16 : ∀ (x : Litex.Object) (h_0_1 : Litex.In x Litex.RPos), Litex.Lt 0 x :=
by
  intro x h_0_1
  have litex_inferred_fact_1 : Litex.Lt 0 x := by
    exact (Litex.Rules.positiveRealMembership h_0_1)
  exact litex_inferred_fact_1
```
<!-- END ACTUAL GENERATED LEAN: inferred_forall_premise -->

Required generated shape:

```lean
theorem fact... :
    ∀ (x : Litex.Object) (h_0_1 : Litex.In x Litex.RPos), Litex.Lt 0 x := by
  intro x h_0_1
  have litex_inferred_fact_1 : Litex.Lt 0 x := by
    exact Litex.Rules.positiveRealMembership h_0_1
  exact litex_inferred_fact_1
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

theorem fact13 : ∀ (a : Litex.Object) (h_0_1 : Litex.IsSet a) (b : Litex.Object) (h_0_2 : Litex.IsSet b) (h_0_3 : a ≠ b), (Litex.listSet [a, b]) = (Litex.listSet [a, b]) :=
by
  intro a h_0_1 b h_0_2 h_0_3
  have wd_0_2 : a ≠ b := by
    exact (h_0_3)
  exact rfl

theorem fact35 : ∀ (a : Litex.Object) (h_0_1 : Litex.IsSet a) (b : Litex.Object) (h_0_2 : Litex.IsSet b) (c : Litex.Object) (h_0_3 : Litex.IsSet c) (h_0_4 : a ≠ b) (h_0_5 : a ≠ c) (h_0_6 : b ≠ c), (Litex.listSet [a, b, c]) = (Litex.listSet [a, b, c]) :=
by
  intro a h_0_1 b h_0_2 c h_0_3 h_0_4 h_0_5 h_0_6
  have wd_0_7 : a ≠ b := by
    exact (h_0_4)
  have wd_0_8 : a ≠ c := by
    exact (h_0_5)
  have wd_0_9 : b ≠ c := by
    exact (h_0_6)
  exact rfl
```
<!-- END ACTUAL GENERATED LEAN: proof_carrying_list_set -->

Lean status: **checked** — the theorem type uses proof-free `Litex.listSet`
terms and its pairwise WD evidence is introduced locally after `intro`.

Required generated shape:

```lean
theorem fact... : Litex.listSet [a, b, c] = Litex.listSet [a, b, c] := by
  intro a h_a b h_b c h_c h_ab h_ac h_bc
  have wd_0_<a_ne_b> : a ≠ b := by exact h_ab
  have wd_0_<a_ne_c> : a ≠ c := by exact h_ac
  have wd_0_<b_ne_c> : b ≠ c := by exact h_bc
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

theorem fact3 : Litex.In x Litex.R := by
  unfold x
  exact Classical.choose_spec (Litex.Rules.realSetNonempty)
```
<!-- END ACTUAL GENERATED LEAN: object_choice -->

Lean uses `Classical.choose` and `choose_spec`; changed carrier or nonemptiness
evidence is rejected instead of inventing a witness.

```lean
noncomputable def x : Litex.Object := Classical.choose <nonempty_R>
theorem fact_<x_in_R> : Litex.In x Litex.R := Classical.choose_spec <nonempty_R>
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

theorem fact8 : ∃ (x : Litex.Object), Litex.In x Litex.R ∧ x = 1 := by
  exact (by
  have litex_exist_step_1 : (1 : Litex.Object) = 1 := by
    exact rfl
  exact ⟨1, (Litex.Rules.numeralInR 1), (litex_exist_step_1)⟩)

noncomputable def y : Litex.Object := Classical.choose (fact8)

theorem fact13 : Litex.In y Litex.R := by
  unfold y
  exact (Classical.choose_spec (fact8)).1

theorem fact14 : y = 1 := by
  unfold y
  exact (Classical.choose_spec (fact8)).2
```
<!-- END ACTUAL GENERATED LEAN: existential_intro_elim -->

Lean uses `Exists.intro`, `Classical.choose`, and `choose_spec`; `exist!`,
negation, and changed projection roles remain rejected boundaries.

```lean
theorem fact_<exist> : ∃ x, Litex.In x Litex.R ∧ x = 1 := by ...
noncomputable def y : Litex.Object := Classical.choose fact_<exist>
theorem fact_<y_in_R> : Litex.In y Litex.R := (Classical.choose_spec fact_<exist>).1
```

## case_and_contradiction_scopes

Case analysis and contradiction keep case and reverse-assumption `FactId`s
local.

```litex
by cases:
    ? 1 = 1
    case 1 = 1
by contra:
    ? 2 = 2
    impossible 2 != 2
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: case_and_contradiction_scopes -->
```lean
import Litex.Rules

theorem fact2 : (1 : Litex.Object) = 1 := by
  exact (by
  have litex_case_1 : (1 : Litex.Object) = 1 := rfl
  exact litex_case_1)

theorem fact4 : (2 : Litex.Object) = 2 := by
  exact (by
  by_contra litex_reverse_assumption
  exact (litex_reverse_assumption) (rfl))
```
<!-- END ACTUAL GENERATED LEAN: case_and_contradiction_scopes -->

A local `FactId` moved to another coverage slot fails closed.

```lean
by_cases litex_case_1 : <case proposition>
by_contra litex_reverse_assumption
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

theorem fact1 : Litex.pi = Litex.pi := by
  exact rfl

theorem fact11 : ∀ (A : Litex.Object) (h_0_1 : Litex.IsSet A) (B : Litex.Object) (h_0_2 : Litex.IsSet B), (Litex.union A B) = (Litex.union A B) :=
by
  intro A h_0_1 B h_0_2
  exact rfl
```
<!-- END ACTUAL GENERATED LEAN: total_object_constructors -->

`Litex.pi` and `Litex.union A B` need no proof arguments. Unsupported constants
and changed arity remain explicit errors.

```lean
theorem fact_<pi> : Litex.pi = Litex.pi := by rfl
theorem fact_<union> ... : Litex.union A B = Litex.union A B := by rfl
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

theorem fact13 : ∀ (a : Litex.Object) (h_0_1 : Litex.In a Litex.C) (b : Litex.Object) (h_0_2 : Litex.In b Litex.C) (h_0_3 : b ≠ 0), (Litex.div a b) = (Litex.div a b) :=
by
  intro a h_0_1 b h_0_2 h_0_3
  have wd_0_4 : b ≠ 0 := by
    exact (h_0_3)
  have wd_0_5 : Litex.In a Litex.C := by
    exact (h_0_1)
  have wd_0_6 : Litex.In b Litex.C := by
    exact (h_0_2)
  have obj_10_result : Litex.In (Litex.div a b) Litex.C := by
    exact ((Litex.Rules.complexDivClosure (wd_0_5) (wd_0_6) (wd_0_4)))
  exact rfl

theorem fact26 : ∀ (a : Litex.Object) (h_0_1 : Litex.In a Litex.R) (b : Litex.Object) (h_0_2 : Litex.In b Litex.R) (h_0_3 : b ≠ 0), Litex.In (Litex.div a b) Litex.R :=
by
  intro a h_0_1 b h_0_2 h_0_3
  have wd_0_15 : b ≠ 0 := by
    exact (h_0_3)
  have wd_0_16 : Litex.In a Litex.R := by
    exact (h_0_1)
  have wd_0_17 : Litex.In a Litex.C := by
    exact ((Litex.Rules.realInComplex (h_0_1)))
  have wd_0_18 : Litex.In b Litex.R := by
    exact (h_0_2)
  have wd_0_19 : Litex.In b Litex.C := by
    exact ((Litex.Rules.realInComplex (h_0_2)))
  have obj_27_result : Litex.In (Litex.div a b) Litex.C := by
    exact ((Litex.Rules.complexDivClosure (wd_0_17) (wd_0_19) (wd_0_15)))
  exact (Litex.Rules.realDivClosure (wd_0_17) (wd_0_19) (wd_0_15) (h_0_1) (h_0_2))
```
<!-- END ACTUAL GENERATED LEAN: proof_carrying_division -->

The Litex source certificate retains two `C` memberships and the exact nonzero
proof; none of the three slots can be deleted, moved, or reconstructed by
target search. The quotient term itself is proof-free.

```lean
theorem fact... : Litex.div a b = Litex.div a b := by
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

noncomputable def S : Litex.Object := (Litex.setBuilder Litex.R (fun litex_set_builder_2 => litex_set_builder_2 = litex_set_builder_2))

theorem fact4 : Litex.IsSet S := by
  simpa only [S] using (Litex.Rules.objectIsSet (Litex.setBuilder Litex.R (fun litex_set_builder_2 => litex_set_builder_2 = litex_set_builder_2)))

theorem fact5 : S = (Litex.setBuilder Litex.R (fun litex_set_builder_2 => litex_set_builder_2 = litex_set_builder_2)) := by
  rfl

theorem fact6 : S = S := by
  exact rfl
```
<!-- END ACTUAL GENERATED LEAN: set_builder_scope -->

Lean emits `Litex.setBuilder ... (fun litex_set_builder_ID => ...)`; the local
binder never leaks and changed identity changes the retained object.

```lean
noncomputable def S : Litex.Object :=
  Litex.setBuilder Litex.R (fun litex_set_builder_<id> =>
    litex_set_builder_<id> = litex_set_builder_<id>)
```

## named_function

A named function emits a dependent requirements telescope, verifier-owned
local `wd_<environment-depth>_<WellDefinedFactId>` body DAG inside its closure
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

noncomputable def litex_id_spec : Litex.FnSpec :=
  ({ arity := 1, requirements := fun litex_function_args => ∃ litex_function_premise_1 : Litex.In (Litex.arg litex_function_args 0) Litex.R, True, range := fun litex_function_args litex_function_length litex_function_requirements => Litex.R } : Litex.FnSpec)

noncomputable def litex_id_body
    (litex_function_args : List Litex.Object)
    (litex_function_length : litex_function_args.length = litex_id_spec.arity)
    (litex_function_requirements : litex_id_spec.requirements litex_function_args) : Litex.Object :=
  (Litex.arg litex_function_args 0)

theorem litex_id_closed :
    ∀ litex_function_args litex_function_length litex_function_requirements,
      Litex.In
        (litex_id_body litex_function_args litex_function_length litex_function_requirements)
        (litex_id_spec.range litex_function_args litex_function_length litex_function_requirements) := by
  intro litex_function_args litex_function_length litex_function_requirements
  change Litex.In (Litex.arg litex_function_args 0) Litex.R
  exact Exists.choose (litex_function_requirements)

noncomputable def litex_id_implementation : Litex.Object :=
  Litex.functionObject litex_id_spec litex_id_body

noncomputable def litex_id : Litex.Object := litex_id_implementation

theorem fact5 : Litex.In litex_id (Litex.FnSet ({ arity := 1, requirements := fun litex_function_args => ∃ litex_function_premise_1 : Litex.In (Litex.arg litex_function_args 0) Litex.R, True, range := fun litex_function_args litex_function_length litex_function_requirements => Litex.R } : Litex.FnSpec)) := by
  simpa only [litex_id, litex_id_implementation, litex_id_spec] using
    (Litex.functionObjectInFnSet litex_id_spec litex_id_body litex_id_closed)

theorem fact6 : litex_id = litex_id_implementation := by
  rfl

theorem fact7 : (litex_id [1]) = 1 := by
  have wd_0_2 : Litex.In 1 Litex.R := by
    exact (Litex.Rules.numeralInR 1)
  have obj_15_applicable : Litex.Applicable (litex_id) [1] := by
    exact (Litex.fnSetApplicable fact5 rfl (by
      change ∃ litex_application_requirement_1 : Litex.In (1) Litex.R, True
      exact Exists.intro (wd_0_2) (True.intro)))
  have obj_15_result : Litex.In (litex_id [1]) Litex.R := by
    exact (by simpa using (Litex.fnSetResult fact5 rfl (by
      change ∃ litex_application_requirement_1 : Litex.In (1) Litex.R, True
      exact Exists.intro (wd_0_2) (True.intro))))
  exact (by
  change ((litex_id) [1]) = 1
  rw [fact6]
  unfold litex_id_implementation
  rw [Litex.functionObject_apply _ _ _ (by
    simpa only [fact6, litex_id_implementation] using obj_15_applicable)]
  simp only [litex_id_body, Litex.arg, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil])

noncomputable def inc_spec : Litex.FnSpec :=
  ({ arity := 1, requirements := fun litex_function_args => ∃ litex_function_premise_1 : Litex.In (Litex.arg litex_function_args 0) Litex.R, True, range := fun litex_function_args litex_function_length litex_function_requirements => Litex.R } : Litex.FnSpec)

noncomputable def inc_body
    (litex_function_args : List Litex.Object)
    (litex_function_length : litex_function_args.length = inc_spec.arity)
    (litex_function_requirements : inc_spec.requirements litex_function_args) : Litex.Object :=
  (Litex.add (Litex.arg litex_function_args 0) 1)

theorem inc_closed :
    ∀ litex_function_args litex_function_length litex_function_requirements,
      Litex.In
        (inc_body litex_function_args litex_function_length litex_function_requirements)
        (inc_spec.range litex_function_args litex_function_length litex_function_requirements) := by
  intro litex_function_args litex_function_length litex_function_requirements
  have wd_0_8 : Litex.In (Litex.arg litex_function_args 0) Litex.R := by
    exact (Exists.choose (litex_function_requirements))
  have wd_0_9 : Litex.In (Litex.arg litex_function_args 0) Litex.C := by
    exact ((Litex.Rules.realInComplex (Exists.choose (litex_function_requirements))))
  have wd_0_10 : Litex.In 1 Litex.C := by
    exact (Litex.Rules.numeralInC 1)
  have obj_24_result : Litex.In (Litex.add (Litex.arg litex_function_args 0) 1) Litex.C := by
    exact ((Litex.Rules.complexAddClosure (wd_0_9) (wd_0_10)))
  change Litex.In (Litex.add (Litex.arg litex_function_args 0) 1) Litex.R
  exact (Litex.Rules.realAddClosure (wd_0_9) (wd_0_10) (Exists.choose (litex_function_requirements)) (Litex.Rules.numeralInR 1))

noncomputable def inc_implementation : Litex.Object :=
  Litex.functionObject inc_spec inc_body

noncomputable def inc : Litex.Object := inc_implementation

theorem fact12 : Litex.In inc (Litex.FnSet ({ arity := 1, requirements := fun litex_function_args => ∃ litex_function_premise_1 : Litex.In (Litex.arg litex_function_args 0) Litex.R, True, range := fun litex_function_args litex_function_length litex_function_requirements => Litex.R } : Litex.FnSpec)) := by
  simpa only [inc, inc_implementation, inc_spec] using
    (Litex.functionObjectInFnSet inc_spec inc_body inc_closed)

theorem fact13 : inc = inc_implementation := by
  rfl

theorem fact14 : (inc [1]) = (Litex.add 1 1) := by
  have wd_0_11 : Litex.In 1 Litex.R := by
    exact (Litex.Rules.numeralInR 1)
  have obj_28_applicable : Litex.Applicable (inc) [1] := by
    exact (Litex.fnSetApplicable fact12 rfl (by
      change ∃ litex_application_requirement_1 : Litex.In (1) Litex.R, True
      exact Exists.intro (wd_0_11) (True.intro)))
  have obj_28_result : Litex.In (inc [1]) Litex.R := by
    exact (by simpa using (Litex.fnSetResult fact12 rfl (by
      change ∃ litex_application_requirement_1 : Litex.In (1) Litex.R, True
      exact Exists.intro (wd_0_11) (True.intro))))
  have wd_0_12 : Litex.In 1 Litex.C := by
    exact (Litex.Rules.numeralInC 1)
  have obj_30_result : Litex.In (Litex.add 1 1) Litex.C := by
    exact ((Litex.Rules.complexAddClosure (wd_0_12) (wd_0_12)))
  exact (by
  change ((inc) [1]) = (Litex.add 1 1)
  rw [fact13]
  unfold inc_implementation
  rw [Litex.functionObject_apply _ _ _ (by
    simpa only [fact13, inc_implementation] using obj_28_applicable)]
  simp only [inc_body, Litex.arg, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil])

noncomputable def reciprocal_spec : Litex.FnSpec :=
  ({ arity := 1, requirements := fun litex_function_args => ∃ litex_function_premise_1 : Litex.In (Litex.arg litex_function_args 0) Litex.R, ∃ litex_function_premise_2 : (Litex.arg litex_function_args 0) ≠ 0, True, range := fun litex_function_args litex_function_length litex_function_requirements => Litex.R } : Litex.FnSpec)

noncomputable def reciprocal_body
    (litex_function_args : List Litex.Object)
    (litex_function_length : litex_function_args.length = reciprocal_spec.arity)
    (litex_function_requirements : reciprocal_spec.requirements litex_function_args) : Litex.Object :=
  (Litex.div 1 (Litex.arg litex_function_args 0))

theorem reciprocal_closed :
    ∀ litex_function_args litex_function_length litex_function_requirements,
      Litex.In
        (reciprocal_body litex_function_args litex_function_length litex_function_requirements)
        (reciprocal_spec.range litex_function_args litex_function_length litex_function_requirements) := by
  intro litex_function_args litex_function_length litex_function_requirements
  have wd_0_19 : (Litex.arg litex_function_args 0) ≠ 0 := by
    exact (Exists.choose (Exists.choose_spec (litex_function_requirements)))
  have wd_0_20 : Litex.In 1 Litex.C := by
    exact (Litex.Rules.numeralInC 1)
  have wd_0_21 : Litex.In (Litex.arg litex_function_args 0) Litex.R := by
    exact (Exists.choose (litex_function_requirements))
  have wd_0_22 : Litex.In (Litex.arg litex_function_args 0) Litex.C := by
    exact ((Litex.Rules.realInComplex (Exists.choose (litex_function_requirements))))
  have obj_39_result : Litex.In (Litex.div 1 (Litex.arg litex_function_args 0)) Litex.C := by
    exact ((Litex.Rules.complexDivClosure (wd_0_20) (wd_0_22) (wd_0_19)))
  change Litex.In (Litex.div 1 (Litex.arg litex_function_args 0)) Litex.R
  exact (Litex.Rules.realDivClosure (wd_0_20) (wd_0_22) (wd_0_19) (Litex.Rules.numeralInR 1) (Exists.choose (litex_function_requirements)))

noncomputable def reciprocal_implementation : Litex.Object :=
  Litex.functionObject reciprocal_spec reciprocal_body

noncomputable def reciprocal : Litex.Object := reciprocal_implementation

theorem fact23 : Litex.In reciprocal (Litex.FnSet ({ arity := 1, requirements := fun litex_function_args => ∃ litex_function_premise_1 : Litex.In (Litex.arg litex_function_args 0) Litex.R, ∃ litex_function_premise_2 : (Litex.arg litex_function_args 0) ≠ 0, True, range := fun litex_function_args litex_function_length litex_function_requirements => Litex.R } : Litex.FnSpec)) := by
  simpa only [reciprocal, reciprocal_implementation, reciprocal_spec] using
    (Litex.functionObjectInFnSet reciprocal_spec reciprocal_body reciprocal_closed)

theorem fact24 : reciprocal = reciprocal_implementation := by
  rfl

theorem fact34 : ∀ (a : Litex.Object) (h_0_1 : Litex.In a Litex.R) (h_0_2 : a ≠ 0), (reciprocal [a]) = (Litex.div 1 a) :=
by
  intro a h_0_1 h_0_2
  have wd_0_28 : Litex.In a Litex.R := by
    exact (h_0_1)
  have wd_0_29 : a ≠ 0 := by
    exact (h_0_2)
  have obj_50_applicable : Litex.Applicable (reciprocal) [a] := by
    exact (Litex.fnSetApplicable fact23 rfl (by
      change ∃ litex_application_requirement_1 : Litex.In (a) Litex.R, ∃ litex_application_requirement_2 : (a) ≠ 0, True
      exact Exists.intro (wd_0_28) (Exists.intro (wd_0_29) (True.intro))))
  have obj_50_result : Litex.In (reciprocal [a]) Litex.R := by
    exact (by simpa using (Litex.fnSetResult fact23 rfl (by
      change ∃ litex_application_requirement_1 : Litex.In (a) Litex.R, ∃ litex_application_requirement_2 : (a) ≠ 0, True
      exact Exists.intro (wd_0_28) (Exists.intro (wd_0_29) (True.intro)))))
  have wd_0_30 : a ≠ 0 := by
    exact (h_0_2)
  have wd_0_31 : Litex.In 1 Litex.C := by
    exact (Litex.Rules.numeralInC 1)
  have wd_0_32 : Litex.In a Litex.C := by
    exact ((Litex.Rules.realInComplex (h_0_1)))
  have obj_51_result : Litex.In (Litex.div 1 a) Litex.C := by
    exact ((Litex.Rules.complexDivClosure (wd_0_31) (wd_0_32) (wd_0_30)))
  exact (by
  change ((reciprocal) [a]) = (Litex.div 1 a)
  rw [fact24]
  unfold reciprocal_implementation
  rw [Litex.functionObject_apply _ _ _ (by
    simpa only [fact24, reciprocal_implementation] using obj_50_applicable)]
  simp only [reciprocal_body, Litex.arg, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil])
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

theorem q_dimension_positive : Litex.In 2 Litex.NPos := by
  exact (Litex.Rules.numeralInNPos 2 (by norm_num))

theorem q_dimension_at_least_two : Litex.Le 2 2 := by
  exact (by
  exact (Litex.Rules.numeralLe 2 2).2 (by norm_num))

noncomputable def q_value (litex_tuple_index_1 : Litex.Object) : Litex.Object :=
  0

noncomputable def q : Litex.Object :=
  Litex.tupleObject 2 q_value q_dimension_positive q_dimension_at_least_two

theorem fact6 : Litex.IsTuple q :=
by
  unfold q
  exact Litex.tupleObjectIsTuple 2 q_value q_dimension_positive q_dimension_at_least_two

theorem fact7 : (Litex.tupleDim q) = 2 :=
by
  simpa only [q] using
    (Litex.tupleObject_dim 2 q_value q_dimension_positive q_dimension_at_least_two)

theorem fact14 : ∀ (_binder_2 : Litex.Object) (h_0_1 : Litex.In _binder_2 (Litex.closedRange 1 2)), (Litex.atIndex q _binder_2) = 0 :=
by
  intro litex_coordinate litex_coordinate_in_range
  simpa only [q, q_value] using
    (Litex.tupleObject_at 2 q_value q_dimension_positive q_dimension_at_least_two litex_coordinate)

theorem fact15 : q = q := by
  exact rfl
```
<!-- END ACTUAL GENERATED LEAN: indexed_aggregate -->

One `Litex.tupleObject` consumes both dimension checks and exports the exact
is-tuple, dimension, and coordinate effects. Other aggregate families remain
separate until reuse is demonstrated.

```lean
noncomputable def q :=
  Litex.tupleObject 2 q_value q_dimension_positive q_dimension_at_least_two
theorem fact_<q_is_tuple> : Litex.IsTuple q := Litex.tupleObjectIsTuple ...
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

noncomputable def litex_id_spec : Litex.FnSpec :=
  ({ arity := 1, requirements := fun litex_function_args => ∃ litex_function_premise_1 : Litex.In (Litex.arg litex_function_args 0) Litex.R, True, range := fun litex_function_args litex_function_length litex_function_requirements => Litex.R } : Litex.FnSpec)

noncomputable def litex_id_body
    (litex_function_args : List Litex.Object)
    (litex_function_length : litex_function_args.length = litex_id_spec.arity)
    (litex_function_requirements : litex_id_spec.requirements litex_function_args) : Litex.Object :=
  (Litex.arg litex_function_args 0)

theorem litex_id_closed :
    ∀ litex_function_args litex_function_length litex_function_requirements,
      Litex.In
        (litex_id_body litex_function_args litex_function_length litex_function_requirements)
        (litex_id_spec.range litex_function_args litex_function_length litex_function_requirements) := by
  intro litex_function_args litex_function_length litex_function_requirements
  change Litex.In (Litex.arg litex_function_args 0) Litex.R
  exact Exists.choose (litex_function_requirements)

noncomputable def litex_id_implementation : Litex.Object :=
  Litex.functionObject litex_id_spec litex_id_body

noncomputable def litex_id : Litex.Object := litex_id_implementation

theorem fact5 : Litex.In litex_id (Litex.FnSet ({ arity := 1, requirements := fun litex_function_args => ∃ litex_function_premise_1 : Litex.In (Litex.arg litex_function_args 0) Litex.R, True, range := fun litex_function_args litex_function_length litex_function_requirements => Litex.R } : Litex.FnSpec)) := by
  simpa only [litex_id, litex_id_implementation, litex_id_spec] using
    (Litex.functionObjectInFnSet litex_id_spec litex_id_body litex_id_closed)

theorem fact6 : litex_id = litex_id_implementation := by
  rfl

theorem fact14 : ∃ (x : Litex.Object), Litex.In x Litex.R ∧ x = 1 := by
  exact (by
  have litex_exist_step_1 : (1 : Litex.Object) = 1 := by
    exact rfl
  exact ⟨1, (Litex.Rules.numeralInR 1), (litex_exist_step_1)⟩)

noncomputable def y : Litex.Object := Classical.choose (fact14)

theorem fact19 : Litex.In y Litex.R := by
  unfold y
  exact (Classical.choose_spec (fact14)).1

theorem fact20 : y = 1 := by
  unfold y
  exact (Classical.choose_spec (fact14)).2

theorem fact21 : (litex_id [y]) = y := by
  have wd_0_2 : Litex.In y Litex.R := by
    exact (fact19)
  have obj_33_applicable : Litex.Applicable (litex_id) [y] := by
    exact (Litex.fnSetApplicable fact5 rfl (by
      change ∃ litex_application_requirement_1 : Litex.In (y) Litex.R, True
      exact Exists.intro (wd_0_2) (True.intro)))
  have obj_33_result : Litex.In (litex_id [y]) Litex.R := by
    exact (by simpa using (Litex.fnSetResult fact5 rfl (by
      change ∃ litex_application_requirement_1 : Litex.In (y) Litex.R, True
      exact Exists.intro (wd_0_2) (True.intro))))
  exact (by
  change ((litex_id) [y]) = y
  rw [fact6]
  unfold litex_id_implementation
  rw [Litex.functionObject_apply _ _ _ (by
    simpa only [fact6, litex_id_implementation] using obj_33_applicable)]
  simp only [litex_id_body, Litex.arg, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil])

theorem one_eq_one_by_cases : (1 : Litex.Object) = 1 :=
by
  have litex_theorem_step_1 : (1 : Litex.Object) = 1 := by
    exact (by
  have litex_case_1 : (1 : Litex.Object) = 1 := rfl
  exact litex_case_1)
  exact rfl

noncomputable def into_builder_spec : Litex.FnSpec :=
  ({ arity := 1, requirements := fun litex_function_args => ∃ litex_function_premise_1 : Litex.In (Litex.arg litex_function_args 0) Litex.R, True, range := fun litex_function_args litex_function_length litex_function_requirements => (Litex.setBuilder Litex.R (fun litex_set_builder_9 => litex_set_builder_9 = litex_set_builder_9)) } : Litex.FnSpec)

noncomputable def into_builder_body
    (litex_function_args : List Litex.Object)
    (litex_function_length : litex_function_args.length = into_builder_spec.arity)
    (litex_function_requirements : into_builder_spec.requirements litex_function_args) : Litex.Object :=
  (Litex.arg litex_function_args 0)

theorem into_builder_closed :
    ∀ litex_function_args litex_function_length litex_function_requirements,
      Litex.In
        (into_builder_body litex_function_args litex_function_length litex_function_requirements)
        (into_builder_spec.range litex_function_args litex_function_length litex_function_requirements) := by
  intro litex_function_args litex_function_length litex_function_requirements
  change Litex.In (Litex.arg litex_function_args 0) (Litex.setBuilder Litex.R (fun litex_set_builder_9 => litex_set_builder_9 = litex_set_builder_9))
  exact (Litex.inSetBuilder_iff.mpr (And.intro (Exists.choose (litex_function_requirements)) ((rfl))))

noncomputable def into_builder_implementation : Litex.Object :=
  Litex.functionObject into_builder_spec into_builder_body

noncomputable def into_builder : Litex.Object := into_builder_implementation

theorem fact40 : Litex.In into_builder (Litex.FnSet ({ arity := 1, requirements := fun litex_function_args => ∃ litex_function_premise_1 : Litex.In (Litex.arg litex_function_args 0) Litex.R, True, range := fun litex_function_args litex_function_length litex_function_requirements => (Litex.setBuilder Litex.R (fun litex_set_builder_9 => litex_set_builder_9 = litex_set_builder_9)) } : Litex.FnSpec)) := by
  simpa only [into_builder, into_builder_implementation, into_builder_spec] using
    (Litex.functionObjectInFnSet into_builder_spec into_builder_body into_builder_closed)

theorem fact41 : into_builder = into_builder_implementation := by
  rfl

theorem fact42 : (into_builder [1]) = 1 := by
  have wd_0_6 : Litex.In 1 Litex.R := by
    exact (Litex.Rules.numeralInR 1)
  have obj_52_applicable : Litex.Applicable (into_builder) [1] := by
    exact (Litex.fnSetApplicable fact40 rfl (by
      change ∃ litex_application_requirement_1 : Litex.In (1) Litex.R, True
      exact Exists.intro (wd_0_6) (True.intro)))
  have obj_52_result : Litex.In (into_builder [1]) (Litex.setBuilder Litex.R (fun litex_set_builder_9 => litex_set_builder_9 = litex_set_builder_9)) := by
    exact (by simpa using (Litex.fnSetResult fact40 rfl (by
      change ∃ litex_application_requirement_1 : Litex.In (1) Litex.R, True
      exact Exists.intro (wd_0_6) (True.intro))))
  exact (by
  change ((into_builder) [1]) = 1
  rw [fact41]
  unfold into_builder_implementation
  rw [Litex.functionObject_apply _ _ _ (by
    simpa only [fact41, into_builder_implementation] using obj_52_applicable)]
  simp only [into_builder_body, Litex.arg, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil])
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

theorem wd_0_3 : ∀ (litex_wd_scope_3_arg_1 : Litex.Object) (litex_wd_scope_3_premise_1 : Litex.In litex_wd_scope_3_arg_1 Litex.R), Litex.In litex_wd_scope_3_arg_1 Litex.R :=
by
  intro litex_wd_scope_3_arg_1 litex_wd_scope_3_premise_1
  exact litex_wd_scope_3_premise_1

theorem wd_0_4 : ∀ (litex_wd_scope_4_arg_1 : Litex.Object) (litex_wd_scope_4_premise_1 : Litex.In litex_wd_scope_4_arg_1 Litex.R), Litex.In litex_wd_scope_4_arg_1 Litex.R :=
by
  intro litex_wd_scope_4_arg_1 litex_wd_scope_4_premise_1
  exact litex_wd_scope_4_premise_1

noncomputable def obj_7 : Litex.Object :=
  Litex.R

noncomputable def obj_8 (litex_wd_scope_3_arg_1 : Litex.Object) : Litex.Object :=
  litex_wd_scope_3_arg_1

noncomputable def obj_9_spec : Litex.FnSpec :=
  ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec)

noncomputable def obj_9_body (litex_obj_9_args : List Litex.Object) (_litex_length : litex_obj_9_args.length = (obj_9_spec).arity) (_litex_requirements : (obj_9_spec).requirements litex_obj_9_args) : Litex.Object :=
  (obj_8 (Litex.arg litex_obj_9_args 0))

theorem obj_9_closed :
    ∀ (litex_obj_9_args : List Litex.Object)
      (litex_obj_9_length : litex_obj_9_args.length = (obj_9_spec).arity)
      (litex_obj_9_requirements : (obj_9_spec).requirements litex_obj_9_args),
      Litex.In (obj_9_body litex_obj_9_args litex_obj_9_length litex_obj_9_requirements) ((obj_9_spec).range litex_obj_9_args litex_obj_9_length litex_obj_9_requirements) :=
by
  intro litex_obj_9_args litex_obj_9_length litex_obj_9_requirements
  change Litex.In (Litex.arg litex_obj_9_args 0) Litex.R
  exact (wd_0_3 (Litex.arg litex_obj_9_args 0) (Exists.choose (litex_obj_9_requirements)))

noncomputable def obj_9 : Litex.Object :=
  Litex.functionObject obj_9_spec obj_9_body

theorem obj_9_in_fn_set :
    Litex.In obj_9 (Litex.FnSet obj_9_spec) := by
  unfold obj_9
  exact Litex.functionObjectInFnSet obj_9_spec obj_9_body obj_9_closed

noncomputable def obj_10 : Litex.Object :=
  Litex.R

noncomputable def obj_11 (litex_wd_scope_4_arg_1 : Litex.Object) : Litex.Object :=
  litex_wd_scope_4_arg_1

noncomputable def obj_12_spec : Litex.FnSpec :=
  ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec)

noncomputable def obj_12_body (litex_obj_12_args : List Litex.Object) (_litex_length : litex_obj_12_args.length = (obj_12_spec).arity) (_litex_requirements : (obj_12_spec).requirements litex_obj_12_args) : Litex.Object :=
  (obj_11 (Litex.arg litex_obj_12_args 0))

theorem obj_12_closed :
    ∀ (litex_obj_12_args : List Litex.Object)
      (litex_obj_12_length : litex_obj_12_args.length = (obj_12_spec).arity)
      (litex_obj_12_requirements : (obj_12_spec).requirements litex_obj_12_args),
      Litex.In (obj_12_body litex_obj_12_args litex_obj_12_length litex_obj_12_requirements) ((obj_12_spec).range litex_obj_12_args litex_obj_12_length litex_obj_12_requirements) :=
by
  intro litex_obj_12_args litex_obj_12_length litex_obj_12_requirements
  change Litex.In (Litex.arg litex_obj_12_args 0) Litex.R
  exact (wd_0_4 (Litex.arg litex_obj_12_args 0) (Exists.choose (litex_obj_12_requirements)))

noncomputable def obj_12 : Litex.Object :=
  Litex.functionObject obj_12_spec obj_12_body

theorem obj_12_in_fn_set :
    Litex.In obj_12 (Litex.FnSet obj_12_spec) := by
  unfold obj_12
  exact Litex.functionObjectInFnSet obj_12_spec obj_12_body obj_12_closed

theorem fact7 : obj_9 = obj_12 := by
  exact rfl

theorem wd_0_11 : ∀ (a : Litex.Object) (h_0_1 : Litex.In a Litex.R) (litex_wd_scope_9_arg_1 : Litex.Object) (litex_wd_scope_9_premise_1 : Litex.In litex_wd_scope_9_arg_1 Litex.R), Litex.In litex_wd_scope_9_arg_1 Litex.R :=
by
  intro a h_0_1 litex_wd_scope_9_arg_1 litex_wd_scope_9_premise_1
  exact litex_wd_scope_9_premise_1

theorem wd_0_12 : ∀ (a : Litex.Object) (h_0_1 : Litex.In a Litex.R), Litex.In a Litex.R :=
by
  intro a h_0_1
  exact h_0_1

noncomputable def obj_27 : Litex.Object :=
  Litex.R

noncomputable def obj_28 (a : Litex.Object) : Litex.Object :=
  a

noncomputable def obj_29 (litex_wd_scope_9_arg_1 : Litex.Object) : Litex.Object :=
  litex_wd_scope_9_arg_1

noncomputable def obj_30_spec (a : Litex.Object) (h_0_1 : Litex.In a Litex.R) : Litex.FnSpec :=
  ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec)

noncomputable def obj_30_body (a : Litex.Object) (h_0_1 : Litex.In a Litex.R) (litex_obj_30_args : List Litex.Object) (_litex_length : litex_obj_30_args.length = ((obj_30_spec a h_0_1)).arity) (_litex_requirements : ((obj_30_spec a h_0_1)).requirements litex_obj_30_args) : Litex.Object :=
  (obj_29 (Litex.arg litex_obj_30_args 0))

theorem obj_30_closed (a : Litex.Object) (h_0_1 : Litex.In a Litex.R) :
    ∀ (litex_obj_30_args : List Litex.Object)
      (litex_obj_30_length : litex_obj_30_args.length = ((obj_30_spec a h_0_1)).arity)
      (litex_obj_30_requirements : ((obj_30_spec a h_0_1)).requirements litex_obj_30_args),
      Litex.In ((obj_30_body a h_0_1) litex_obj_30_args litex_obj_30_length litex_obj_30_requirements) (((obj_30_spec a h_0_1)).range litex_obj_30_args litex_obj_30_length litex_obj_30_requirements) :=
by
  intro litex_obj_30_args litex_obj_30_length litex_obj_30_requirements
  change Litex.In (Litex.arg litex_obj_30_args 0) Litex.R
  exact (wd_0_11 (a) (h_0_1) (Litex.arg litex_obj_30_args 0) (Exists.choose (litex_obj_30_requirements)))

noncomputable def obj_30 (a : Litex.Object) (h_0_1 : Litex.In a Litex.R) : Litex.Object :=
  Litex.functionObject (obj_30_spec a h_0_1) (obj_30_body a h_0_1)

theorem obj_30_in_fn_set (a : Litex.Object) (h_0_1 : Litex.In a Litex.R) :
    Litex.In (obj_30 a h_0_1) (Litex.FnSet (obj_30_spec a h_0_1)) := by
  unfold obj_30
  exact Litex.functionObjectInFnSet (obj_30_spec a h_0_1) (obj_30_body a h_0_1) (obj_30_closed a h_0_1)

theorem obj_31_applicable : ∀ (a : Litex.Object) (h_0_1 : Litex.In a Litex.R), Litex.Applicable (obj_30 a h_0_1) [(obj_28 a)] :=
by
  intro a h_0_1
  exact Litex.fnSetApplicable (obj_30_in_fn_set a h_0_1) rfl (by
  change ∃ litex_application_requirement_1 : Litex.In ((obj_28 a)) Litex.R, True
  exact Exists.intro ((wd_0_12 a h_0_1)) (True.intro))

noncomputable def obj_31 (a : Litex.Object) (h_0_1 : Litex.In a Litex.R) : Litex.Object :=
  (obj_30 a h_0_1) [(obj_28 a)]

theorem obj_31_result : ∀ (a : Litex.Object) (h_0_1 : Litex.In a Litex.R), Litex.In (obj_31 a h_0_1) Litex.R :=
by
  intro a h_0_1
  simpa [obj_31] using (Litex.fnSetResult (obj_30_in_fn_set a h_0_1) rfl (by
  change ∃ litex_application_requirement_1 : Litex.In ((obj_28 a)) Litex.R, True
  exact Exists.intro ((wd_0_12 a h_0_1)) (True.intro)))

theorem wd_0_13 : ∀ (a : Litex.Object) (h_0_1 : Litex.In a Litex.R) (litex_wd_scope_10_arg_1 : Litex.Object) (litex_wd_scope_10_premise_1 : Litex.In litex_wd_scope_10_arg_1 Litex.R), Litex.In litex_wd_scope_10_arg_1 Litex.R :=
by
  intro a h_0_1 litex_wd_scope_10_arg_1 litex_wd_scope_10_premise_1
  exact litex_wd_scope_10_premise_1

theorem wd_0_14 : ∀ (a : Litex.Object) (h_0_1 : Litex.In a Litex.R), Litex.In a Litex.R :=
by
  intro a h_0_1
  exact h_0_1

noncomputable def obj_32 (litex_wd_scope_10_arg_1 : Litex.Object) : Litex.Object :=
  litex_wd_scope_10_arg_1

noncomputable def obj_33_spec (a : Litex.Object) (h_0_1 : Litex.In a Litex.R) : Litex.FnSpec :=
  ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec)

noncomputable def obj_33_body (a : Litex.Object) (h_0_1 : Litex.In a Litex.R) (litex_obj_33_args : List Litex.Object) (_litex_length : litex_obj_33_args.length = ((obj_33_spec a h_0_1)).arity) (_litex_requirements : ((obj_33_spec a h_0_1)).requirements litex_obj_33_args) : Litex.Object :=
  (obj_32 (Litex.arg litex_obj_33_args 0))

theorem obj_33_closed (a : Litex.Object) (h_0_1 : Litex.In a Litex.R) :
    ∀ (litex_obj_33_args : List Litex.Object)
      (litex_obj_33_length : litex_obj_33_args.length = ((obj_33_spec a h_0_1)).arity)
      (litex_obj_33_requirements : ((obj_33_spec a h_0_1)).requirements litex_obj_33_args),
      Litex.In ((obj_33_body a h_0_1) litex_obj_33_args litex_obj_33_length litex_obj_33_requirements) (((obj_33_spec a h_0_1)).range litex_obj_33_args litex_obj_33_length litex_obj_33_requirements) :=
by
  intro litex_obj_33_args litex_obj_33_length litex_obj_33_requirements
  change Litex.In (Litex.arg litex_obj_33_args 0) Litex.R
  exact (wd_0_13 (a) (h_0_1) (Litex.arg litex_obj_33_args 0) (Exists.choose (litex_obj_33_requirements)))

noncomputable def obj_33 (a : Litex.Object) (h_0_1 : Litex.In a Litex.R) : Litex.Object :=
  Litex.functionObject (obj_33_spec a h_0_1) (obj_33_body a h_0_1)

theorem obj_33_in_fn_set (a : Litex.Object) (h_0_1 : Litex.In a Litex.R) :
    Litex.In (obj_33 a h_0_1) (Litex.FnSet (obj_33_spec a h_0_1)) := by
  unfold obj_33
  exact Litex.functionObjectInFnSet (obj_33_spec a h_0_1) (obj_33_body a h_0_1) (obj_33_closed a h_0_1)

theorem obj_34_applicable : ∀ (a : Litex.Object) (h_0_1 : Litex.In a Litex.R), Litex.Applicable (obj_33 a h_0_1) [(obj_28 a)] :=
by
  intro a h_0_1
  exact Litex.fnSetApplicable (obj_33_in_fn_set a h_0_1) rfl (by
  change ∃ litex_application_requirement_1 : Litex.In ((obj_28 a)) Litex.R, True
  exact Exists.intro ((wd_0_14 a h_0_1)) (True.intro))

noncomputable def obj_34 (a : Litex.Object) (h_0_1 : Litex.In a Litex.R) : Litex.Object :=
  (obj_33 a h_0_1) [(obj_28 a)]

theorem obj_34_result : ∀ (a : Litex.Object) (h_0_1 : Litex.In a Litex.R), Litex.In (obj_34 a h_0_1) Litex.R :=
by
  intro a h_0_1
  simpa [obj_34] using (Litex.fnSetResult (obj_33_in_fn_set a h_0_1) rfl (by
  change ∃ litex_application_requirement_1 : Litex.In ((obj_28 a)) Litex.R, True
  exact Exists.intro ((wd_0_14 a h_0_1)) (True.intro)))

theorem fact20 : ∀ (a : Litex.Object) (h_0_1 : Litex.In a Litex.R), (obj_31 a h_0_1) = (obj_34 a h_0_1) :=
by
  intro a h_0_1
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

theorem fact22 : ∀ (f : Litex.Object) (h_0_1 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (h_0_2 : ∀ (y : Litex.Object) (h_1_1 : Litex.In y Litex.R), (f [y]) = (f [(Litex.sub y 1)])), (f [2]) = (f [1]) :=
by
  intro f h_0_1 h_0_2
  have litex_scope_wd_1_8_obj_29_result : ∀ (y : Litex.Object) (h_1_1 : Litex.In y Litex.R), Litex.In y Litex.R ∧ (Litex.Applicable (f) [y] ∧ (Litex.In (f [y]) Litex.R)) := by
    exact (by
      intro y h_1_1
      have wd_1_8 : Litex.In y Litex.R := by
        exact (h_1_1)
      have obj_29_applicable : Litex.Applicable (f) [y] := by
        exact (Litex.fnSetApplicable h_0_1 rfl (by
          change ∃ litex_application_requirement_1 : Litex.In (y) Litex.R, True
          exact Exists.intro (wd_1_8) (True.intro)))
      have obj_29_result : Litex.In (f [y]) Litex.R := by
        exact (by simpa using (Litex.fnSetResult h_0_1 rfl (by
          change ∃ litex_application_requirement_1 : Litex.In (y) Litex.R, True
          exact Exists.intro (wd_1_8) (True.intro))))
      exact And.intro (wd_1_8) (And.intro (obj_29_applicable) ((obj_29_result))))
  have litex_scope_wd_1_9_obj_33_result : ∀ (y : Litex.Object) (h_1_1 : Litex.In y Litex.R), Litex.In y Litex.C ∧ (Litex.In 1 Litex.C ∧ (Litex.In 1 Litex.R ∧ (Litex.In (Litex.sub y 1) Litex.R ∧ (Litex.In (Litex.sub y 1) Litex.C ∧ (Litex.Applicable (f) [(Litex.sub y 1)] ∧ (Litex.In (f [(Litex.sub y 1)]) Litex.R)))))) := by
    exact (by
      intro y h_1_1
      have wd_1_9 : Litex.In y Litex.C := by
        exact ((Litex.Rules.realInComplex (h_1_1)))
      have wd_1_10 : Litex.In 1 Litex.C := by
        exact (Litex.Rules.numeralInC 1)
      have wd_1_11 : Litex.In 1 Litex.R := by
        exact (Litex.Rules.numeralInR 1)
      have wd_1_12 : Litex.In (Litex.sub y 1) Litex.R := by
        exact ((Litex.Rules.realSubClosure (wd_1_9) (wd_1_10) (h_1_1) (Litex.Rules.numeralInR 1)))
      have obj_32_result : Litex.In (Litex.sub y 1) Litex.C := by
        exact ((Litex.Rules.complexSubClosure (wd_1_9) (wd_1_10)))
      have obj_33_applicable : Litex.Applicable (f) [(Litex.sub y 1)] := by
        exact (Litex.fnSetApplicable h_0_1 rfl (by
          change ∃ litex_application_requirement_1 : Litex.In ((Litex.sub y 1)) Litex.R, True
          exact Exists.intro (wd_1_12) (True.intro)))
      have obj_33_result : Litex.In (f [(Litex.sub y 1)]) Litex.R := by
        exact (by simpa using (Litex.fnSetResult h_0_1 rfl (by
          change ∃ litex_application_requirement_1 : Litex.In ((Litex.sub y 1)) Litex.R, True
          exact Exists.intro (wd_1_12) (True.intro))))
      exact And.intro (wd_1_9) (And.intro (wd_1_10) (And.intro (wd_1_11) (And.intro (wd_1_12) (And.intro (obj_32_result) (And.intro (obj_33_applicable) ((obj_33_result))))))))
  have wd_0_13 : Litex.In 2 Litex.R := by
    exact (Litex.Rules.numeralInR 2)
  have obj_36_applicable : Litex.Applicable (f) [2] := by
    exact (Litex.fnSetApplicable h_0_1 rfl (by
      change ∃ litex_application_requirement_1 : Litex.In (2) Litex.R, True
      exact Exists.intro (wd_0_13) (True.intro)))
  have obj_36_result : Litex.In (f [2]) Litex.R := by
    exact (by simpa using (Litex.fnSetResult h_0_1 rfl (by
      change ∃ litex_application_requirement_1 : Litex.In (2) Litex.R, True
      exact Exists.intro (wd_0_13) (True.intro))))
  have wd_0_14 : Litex.In 1 Litex.R := by
    exact (Litex.Rules.numeralInR 1)
  have obj_38_applicable : Litex.Applicable (f) [1] := by
    exact (Litex.fnSetApplicable h_0_1 rfl (by
      change ∃ litex_application_requirement_1 : Litex.In (1) Litex.R, True
      exact Exists.intro (wd_0_14) (True.intro)))
  have obj_38_result : Litex.In (f [1]) Litex.R := by
    exact (by simpa using (Litex.fnSetResult h_0_1 rfl (by
      change ∃ litex_application_requirement_1 : Litex.In (1) Litex.R, True
      exact Exists.intro (wd_0_14) (True.intro))))
  exact (by
  have litex_normalization_source := ((h_0_2 (Litex.add 1 1) ((Litex.Rules.realAddClosure ((Litex.Rules.numeralInC 1)) ((Litex.Rules.numeralInC 1)) (Litex.Rules.numeralInR 1) (Litex.Rules.numeralInR 1)))))
  simp only [OfNat.ofNat, Litex.add_embedComplex, Litex.sub_embedComplex, Litex.mul_embedComplex, Litex.div_embedComplex] at litex_normalization_source ⊢
  norm_num at litex_normalization_source ⊢
  exact litex_normalization_source)
```
<!-- END ACTUAL GENERATED LEAN: arithmetic_forall_wd -->

Required generated shape:

```lean
theorem fact_<forall> : ∀ (f : Litex.Object), ... := by
  intro f h_f h_nested
  have litex_scope_... : ∀ y h_y, ... := by
    intro y h_y
    have wd_1_<sub> : Litex.In (Litex.sub y 1) Litex.R := by
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

theorem fact3 : is_zero 0 := by
  exact (by
  change Litex.In 0 Litex.R ∧ ((0 : Litex.Object) = 0)
  exact And.intro (Litex.Rules.numeralInR 0) ((rfl)))

theorem fact4 : Litex.In 0 Litex.R := by
  exact (by
  have litex_definition_source := (fact3)
  change Litex.In 0 Litex.R ∧ ((0 : Litex.Object) = 0) at litex_definition_source
  exact (litex_definition_source).1)

theorem fact5 : (0 : Litex.Object) = 0 := by
  exact (by
  have litex_definition_source := (fact3)
  change Litex.In 0 Litex.R ∧ ((0 : Litex.Object) = 0) at litex_definition_source
  exact (litex_definition_source).2)

noncomputable def named_zero : Litex.Object := 0

theorem fact7 : Litex.In named_zero Litex.R := by
  simpa only [named_zero] using (fact4)

theorem fact8 : named_zero = 0 := by
  rfl

theorem fact9 : is_zero named_zero := by
  exact (by
  change Litex.In named_zero Litex.R ∧ (named_zero = 0)
  exact And.intro (fact7) ((fact8)))

axiom fact10 : marked named_zero
```
<!-- END ACTUAL GENERATED LEAN: first_statement_tranche -->

Required generated shape:

```lean
axiom marked : Litex.Object → Prop
def is_zero (x : Litex.Object) : Prop := Litex.In x Litex.R ∧ x = 0
noncomputable def named_zero : Litex.Object := 0
axiom fact_<trusted> : marked named_zero
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

theorem fact13 : ∀ (a : Litex.Object) (h_0_1 : Litex.IsSet a) (b : Litex.Object) (h_0_2 : Litex.IsSet b) (h_0_3 : a = b), b = a :=
by
  intro a h_0_1 b h_0_2 h_0_3
  exact (Eq.symm (h_0_3))

theorem fact32 : ∀ (a : Litex.Object) (h_0_1 : Litex.IsSet a) (b : Litex.Object) (h_0_2 : Litex.IsSet b) (c : Litex.Object) (h_0_3 : Litex.IsSet c) (h_0_4 : a = b) (h_0_5 : b = c), a = c :=
by
  intro a h_0_1 b h_0_2 c h_0_3 h_0_4 h_0_5
  exact (Eq.trans ((h_0_4)) ((h_0_5)))
```
<!-- END ACTUAL GENERATED LEAN: known_equality_path -->

Required generated shape:

```lean
theorem fact_<symm> ... : b = a := by
  exact Eq.symm fact_<a_eq_b>

theorem fact_<trans> ... : a = c := by
  exact Eq.trans fact_<a_eq_b> fact_<b_eq_c>
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

theorem fact27 : ∀ (a : Litex.Object) (h_0_1 : Litex.In a Litex.C) (h_0_2 : a = 1), Litex.In 1 Litex.R :=
by
  intro a h_0_1 h_0_2
  exact Litex.Rules.numeralInR 1

theorem fact28 : ∀ (a : Litex.Object) (h_0_1 : Litex.In a Litex.C) (h_0_2 : a = 1), Litex.In a Litex.R :=
by
  intro a h_0_1 h_0_2
  exact by simpa only [h_0_2] using (fact27 a h_0_1 h_0_2)

theorem fact26 : ∀ (a : Litex.Object) (h_0_1 : Litex.In a Litex.C) (f : Litex.Object) (h_0_2 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (h_0_3 : a = 1), (f [a]) = (f [a]) :=
by
  intro a h_0_1 f h_0_2 h_0_3
  have wd_0_2 : Litex.In a Litex.R := by
    exact (by simpa only [h_0_3] using (fact27 a h_0_1 h_0_3))
  have wd_0_3 : Litex.In a Litex.R := by
    exact (fact28 a h_0_1 h_0_3)
  have obj_24_applicable : Litex.Applicable (f) [a] := by
    exact (Litex.fnSetApplicable h_0_2 rfl (by
      change ∃ litex_application_requirement_1 : Litex.In (a) Litex.R, True
      exact Exists.intro (wd_0_3) (True.intro)))
  have obj_24_result : Litex.In (f [a]) Litex.R := by
    exact (by simpa using (Litex.fnSetResult h_0_2 rfl (by
      change ∃ litex_application_requirement_1 : Litex.In (a) Litex.R, True
      exact Exists.intro (wd_0_3) (True.intro))))
  exact rfl
```
<!-- END ACTUAL GENERATED LEAN: litex_object_abi -->

Required generated shape:

```lean
theorem fact_<forall> :
    ∀ (a : Litex.Object) (_ : Litex.In a Litex.C)
      (f : Litex.Object) (_ : Litex.In f (Litex.FnSet ...)),
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

theorem fact13 : ∀ (s : Litex.Object) (h_0_1 : Litex.IsNonemptySet s), s = s :=
by
  intro s h_0_1
  exact rfl

theorem fact14 : ∀ (t : Litex.Object) (h_0_1 : Litex.IsFiniteSet t), t = t :=
by
  intro t h_0_1
  exact rfl
```
<!-- END ACTUAL GENERATED LEAN: set_predicate_definitions -->

Required generated shape:

```lean
theorem fact_<forall> :
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

theorem fact13 : ∀ (a : Litex.Object) (h_0_1 : Litex.IsSet a) (b : Litex.Object) (h_0_2 : Litex.IsSet b) (h_0_3 : a ≠ b), b ≠ a :=
by
  intro a h_0_1 b h_0_2 h_0_3
  exact (Litex.Rules.notEqualSymmetry (h_0_3))

theorem fact14 : Litex.In 1 Litex.N := by
  exact Litex.Rules.numeralInN 1

theorem fact15 : Litex.Le 0 1 := by
  exact (by
  exact (Litex.Rules.numeralLe 0 1).2 (by norm_num))

theorem fact17 : Litex.In 1 Litex.C := by
  exact Litex.Rules.numeralInC 1
```
<!-- END ACTUAL GENERATED LEAN: shared_builtin_rules -->

Required generated shape:

```lean
import Litex.Rules

exact Litex.Rules.notEqualSymmetry fact_<a_ne_b>
exact Litex.Rules.numeralInN 1
exact Litex.Rules.numeralInC 1
```

Boundary: a verifier builtin without a checked shared-theorem adapter remains
unsupported; the compiler does not generate an inline proof or axiom fallback.
