# Litex-to-Lean executable feature ledger

This file records the currently supported Litex-to-Lean mappings. Each section
contains a self-contained Litex program, the complete Lean file actually
emitted by the current compiler, a compact required shape, and the nearest
rejected boundary. The required shape summarizes the output; it is not a
substitute for the complete generated file.

Generated output uses ABI version 8 and one `Litex.Object` universe. No entry
may reintroduce native numeric binders, `Set ℝ`, carrier unification, widening,
downcasts, target-side proof search, `sorry`, or a compiler-invented axiom.

## well_defined_object_dag

This first entry records verifier-owned well-defined object identities. The two
inner applications must be emitted before the outer application, and the two
equal source occurrences must reuse the same frozen outer object identity.

```litex
forall a, b R, g fn(x R) R, t fn(x R) R, f fn(x, y R) R:
    f(g(a), t(b)) = f(g(a), t(b))
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: well_defined_object_dag -->
```lean
import Litex.BuiltinRules

example : Litex.abiVersion = 8 := rfl

theorem well_defined_fact_7 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, ∃ litex_requirement_2 : Litex.In (Litex.arg litex_args_0 1) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))), Litex.In a Litex.R :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5
  exact litex_param_fact_1

noncomputable def obj_25 (a : Litex.Object) : Litex.Object :=
  a

theorem obj_44_applicable : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, ∃ litex_requirement_2 : Litex.In (Litex.arg litex_args_0 1) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))), Litex.Applicable g [(obj_25 a)] :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5
  exact Litex.fnSetApplicable litex_param_fact_3 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In ((obj_25 a)) Litex.R, True
  exact Exists.intro ((well_defined_fact_7 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5)) (True.intro))

noncomputable def obj_44 (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, ∃ litex_requirement_2 : Litex.In (Litex.arg litex_args_0 1) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) : Litex.Object :=
  g [(obj_25 a)] ((obj_44_applicable a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5))

theorem obj_44_result : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, ∃ litex_requirement_2 : Litex.In (Litex.arg litex_args_0 1) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))), Litex.In (obj_44 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5) Litex.R :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5
  simpa [obj_44] using (Litex.fnSetResult litex_param_fact_3 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In ((obj_25 a)) Litex.R, True
  exact Exists.intro ((well_defined_fact_7 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5)) (True.intro)))

theorem well_defined_fact_8 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, ∃ litex_requirement_2 : Litex.In (Litex.arg litex_args_0 1) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))), Litex.In b Litex.R :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5
  exact litex_param_fact_2

noncomputable def obj_26 (b : Litex.Object) : Litex.Object :=
  b

theorem obj_45_applicable : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, ∃ litex_requirement_2 : Litex.In (Litex.arg litex_args_0 1) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))), Litex.Applicable t [(obj_26 b)] :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5
  exact Litex.fnSetApplicable litex_param_fact_4 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In ((obj_26 b)) Litex.R, True
  exact Exists.intro ((well_defined_fact_8 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5)) (True.intro))

noncomputable def obj_45 (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, ∃ litex_requirement_2 : Litex.In (Litex.arg litex_args_0 1) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) : Litex.Object :=
  t [(obj_26 b)] ((obj_45_applicable a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5))

theorem obj_45_result : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, ∃ litex_requirement_2 : Litex.In (Litex.arg litex_args_0 1) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))), Litex.In (obj_45 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5) Litex.R :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5
  simpa [obj_45] using (Litex.fnSetResult litex_param_fact_4 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In ((obj_26 b)) Litex.R, True
  exact Exists.intro ((well_defined_fact_8 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5)) (True.intro)))

theorem well_defined_fact_9 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, ∃ litex_requirement_2 : Litex.In (Litex.arg litex_args_0 1) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))), Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec)) :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5
  exact litex_param_fact_3

theorem well_defined_fact_10 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, ∃ litex_requirement_2 : Litex.In (Litex.arg litex_args_0 1) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))), Litex.In (g [a] (Litex.fnSetApplicable litex_param_fact_3 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In (a) Litex.R, True
  exact Exists.intro ((well_defined_fact_7 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5)) (True.intro)))) Litex.R :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5
  exact (by simpa using (Litex.fnSetResult litex_param_fact_3 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In (a) Litex.R, True
  exact Exists.intro ((well_defined_fact_7 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5)) (True.intro))))

theorem well_defined_fact_11 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, ∃ litex_requirement_2 : Litex.In (Litex.arg litex_args_0 1) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))), Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec)) :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5
  exact litex_param_fact_4

theorem well_defined_fact_12 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, ∃ litex_requirement_2 : Litex.In (Litex.arg litex_args_0 1) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))), Litex.In (t [b] (Litex.fnSetApplicable litex_param_fact_4 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In (b) Litex.R, True
  exact Exists.intro ((well_defined_fact_8 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5)) (True.intro)))) Litex.R :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5
  exact (by simpa using (Litex.fnSetResult litex_param_fact_4 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In (b) Litex.R, True
  exact Exists.intro ((well_defined_fact_8 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5)) (True.intro))))

noncomputable def obj_24 : Litex.Object :=
  Litex.R

theorem obj_46_applicable : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, ∃ litex_requirement_2 : Litex.In (Litex.arg litex_args_0 1) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))), Litex.Applicable f [(obj_44 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5), (obj_45 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5)] :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5
  exact Litex.fnSetApplicable litex_param_fact_5 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In ((obj_44 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5)) Litex.R, ∃ litex_application_requirement_2 : Litex.In ((obj_45 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5)) Litex.R, True
  exact Exists.intro ((well_defined_fact_10 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5)) (Exists.intro ((well_defined_fact_12 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5)) (True.intro)))

noncomputable def obj_46 (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, ∃ litex_requirement_2 : Litex.In (Litex.arg litex_args_0 1) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) : Litex.Object :=
  f [(obj_44 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5), (obj_45 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5)] ((obj_46_applicable a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5))

theorem obj_46_result : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, ∃ litex_requirement_2 : Litex.In (Litex.arg litex_args_0 1) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))), Litex.In (obj_46 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5) Litex.R :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5
  simpa [obj_46] using (Litex.fnSetResult litex_param_fact_5 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In ((obj_44 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5)) Litex.R, ∃ litex_application_requirement_2 : Litex.In ((obj_45 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5)) Litex.R, True
  exact Exists.intro ((well_defined_fact_10 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5)) (Exists.intro ((well_defined_fact_12 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5)) (True.intro))))

theorem fact43 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, ∃ litex_requirement_2 : Litex.In (Litex.arg litex_args_0 1) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))), (obj_46 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5) = (obj_46 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5) :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5
  exact rfl
```
<!-- END ACTUAL GENERATED LEAN: well_defined_object_dag -->

Required generated shape:

```lean
noncomputable def obj_<g> ... := g [a] ...
noncomputable def obj_<t> ... := t [b] ...
noncomputable def obj_<outer> ... := f [obj_<g>, obj_<t>] ...

theorem fact... : obj_<outer> ... = obj_<outer> ... := by
  rfl
```

Each selected `WellDefinedObjId` owns one `obj_N`, application applicability is
named by `obj_N_applicable`, and verifier propositions remain separately named
by `well_defined_fact_N`. The emitter follows the retained child roles and
order; it does not reconstruct the application DAG from rendered source text.

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
import Litex.BuiltinRules

example : Litex.abiVersion = 8 := rfl

axiom p : Litex.Object → Prop

axiom fact3 : ∀ (x : Litex.Object) (litex_param_fact_1 : Litex.In x Litex.R), p x

theorem fact4 : p 1 := by
  exact (fact3 1 (Litex.BuiltinRules.numeralInR 1))
```
<!-- END ACTUAL GENERATED LEAN: trusted_forall_atomic_fact -->

Required generated shape:

```lean
axiom p : Litex.Object → Prop
axiom fact... :
  ∀ (x : Litex.Object) (_ : Litex.In x Litex.R), p x

theorem fact... : p 1 := by
  exact (fact... 1 (Litex.BuiltinRules.numeralInR 1))
```

The parentheses around the membership proof are semantically required: the
Lean elaborator must receive the applied theorem
`Litex.BuiltinRules.numeralInR 1`, not the unapplied theorem family. An
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
import Litex.BuiltinRules

example : Litex.abiVersion = 8 := rfl

theorem well_defined_fact_5 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (c : Litex.Object) (litex_param_fact_3 : Litex.In c Litex.C), Litex.In a Litex.C :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3
  exact litex_param_fact_1

theorem well_defined_fact_6 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (c : Litex.Object) (litex_param_fact_3 : Litex.In c Litex.C), Litex.In b Litex.C :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3
  exact litex_param_fact_2

theorem well_defined_fact_7 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (c : Litex.Object) (litex_param_fact_3 : Litex.In c Litex.C), Litex.In (Litex.add a b (well_defined_fact_5 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3) (well_defined_fact_6 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3)) Litex.C :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3
  exact (Litex.BuiltinRules.complexAddClosure ((well_defined_fact_5 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3)) ((well_defined_fact_6 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3)))

theorem well_defined_fact_8 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (c : Litex.Object) (litex_param_fact_3 : Litex.In c Litex.C), Litex.In c Litex.C :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3
  exact litex_param_fact_3

noncomputable def obj_7 : Litex.Object :=
  Litex.C

noncomputable def obj_8 (a : Litex.Object) : Litex.Object :=
  a

noncomputable def obj_9 (b : Litex.Object) : Litex.Object :=
  b

noncomputable def obj_10 (c : Litex.Object) : Litex.Object :=
  c

noncomputable def obj_11 (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (c : Litex.Object) (litex_param_fact_3 : Litex.In c Litex.C) : Litex.Object :=
  (Litex.add (obj_8 a) (obj_9 b) (well_defined_fact_5 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3) (well_defined_fact_6 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3))

noncomputable def obj_12 (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (c : Litex.Object) (litex_param_fact_3 : Litex.In c Litex.C) : Litex.Object :=
  (Litex.add (obj_11 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3) (obj_10 c) (well_defined_fact_7 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3) (well_defined_fact_8 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3))

theorem fact13 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (c : Litex.Object) (litex_param_fact_3 : Litex.In c Litex.C), (obj_12 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3) = (obj_12 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3) :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3
  exact rfl

theorem well_defined_fact_19 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (c : Litex.Object) (litex_param_fact_3 : Litex.In c Litex.C), Litex.In a Litex.C :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3
  exact litex_param_fact_1

theorem well_defined_fact_20 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (c : Litex.Object) (litex_param_fact_3 : Litex.In c Litex.C), Litex.In b Litex.C :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3
  exact litex_param_fact_2

theorem well_defined_fact_21 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (c : Litex.Object) (litex_param_fact_3 : Litex.In c Litex.C), Litex.In (Litex.sub a b (well_defined_fact_19 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3) (well_defined_fact_20 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3)) Litex.C :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3
  exact (Litex.BuiltinRules.complexSubClosure ((well_defined_fact_19 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3)) ((well_defined_fact_20 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3)))

theorem well_defined_fact_22 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (c : Litex.Object) (litex_param_fact_3 : Litex.In c Litex.C), Litex.In c Litex.C :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3
  exact litex_param_fact_3

theorem well_defined_fact_23 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (c : Litex.Object) (litex_param_fact_3 : Litex.In c Litex.C), Litex.In (Litex.mul (Litex.sub a b (well_defined_fact_19 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3) (well_defined_fact_20 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3)) c (well_defined_fact_21 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3) (well_defined_fact_22 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3)) Litex.C :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3
  exact (Litex.BuiltinRules.complexMulClosure ((well_defined_fact_21 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3)) ((well_defined_fact_22 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3)))

theorem well_defined_fact_24 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (c : Litex.Object) (litex_param_fact_3 : Litex.In c Litex.C), Litex.In a Litex.C :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3
  exact litex_param_fact_1

noncomputable def obj_26 : Litex.Object :=
  Litex.C

noncomputable def obj_27 (a : Litex.Object) : Litex.Object :=
  a

noncomputable def obj_28 (b : Litex.Object) : Litex.Object :=
  b

noncomputable def obj_29 (c : Litex.Object) : Litex.Object :=
  c

noncomputable def obj_30 (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (c : Litex.Object) (litex_param_fact_3 : Litex.In c Litex.C) : Litex.Object :=
  (Litex.sub (obj_27 a) (obj_28 b) (well_defined_fact_19 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3) (well_defined_fact_20 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3))

noncomputable def obj_31 (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (c : Litex.Object) (litex_param_fact_3 : Litex.In c Litex.C) : Litex.Object :=
  (Litex.mul (obj_30 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3) (obj_29 c) (well_defined_fact_21 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3) (well_defined_fact_22 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3))

noncomputable def obj_32 (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (c : Litex.Object) (litex_param_fact_3 : Litex.In c Litex.C) : Litex.Object :=
  (Litex.add (obj_31 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3) (obj_27 a) (well_defined_fact_23 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3) (well_defined_fact_24 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3))

theorem fact26 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (c : Litex.Object) (litex_param_fact_3 : Litex.In c Litex.C), (obj_32 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3) = (obj_32 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3) :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3
  exact rfl

theorem well_defined_fact_34 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (litex_domain_fact_1 : b ≠ 0), b ≠ 0 :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact litex_domain_fact_1

theorem well_defined_fact_35 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (litex_domain_fact_1 : b ≠ 0), Litex.In a Litex.C :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact litex_param_fact_1

theorem well_defined_fact_36 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (litex_domain_fact_1 : b ≠ 0), Litex.In b Litex.C :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact litex_param_fact_2

noncomputable def obj_46 (a : Litex.Object) : Litex.Object :=
  a

noncomputable def obj_47 (b : Litex.Object) : Litex.Object :=
  b

noncomputable def obj_49 (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (litex_domain_fact_1 : b ≠ 0) : Litex.Object :=
  (Litex.div (obj_46 a) (obj_47 b) (well_defined_fact_35 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) (well_defined_fact_36 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) (well_defined_fact_34 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1))

theorem fact39 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (litex_domain_fact_1 : b ≠ 0), (obj_49 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) = (obj_49 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact rfl

theorem well_defined_fact_45 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (litex_domain_fact_1 : b ≠ 0), b ≠ 0 :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact litex_domain_fact_1

theorem well_defined_fact_46 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (litex_domain_fact_1 : b ≠ 0), Litex.In a Litex.C :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact litex_param_fact_1

theorem well_defined_fact_47 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (litex_domain_fact_1 : b ≠ 0), Litex.In b Litex.C :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact litex_param_fact_2

theorem well_defined_fact_48 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (litex_domain_fact_1 : b ≠ 0), Litex.In (Litex.div a b (well_defined_fact_46 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) (well_defined_fact_47 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) (well_defined_fact_45 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1)) Litex.C :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact (Litex.BuiltinRules.complexDivClosure ((well_defined_fact_46 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1)) ((well_defined_fact_47 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1)) ((well_defined_fact_45 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1)))

theorem well_defined_fact_49 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (litex_domain_fact_1 : b ≠ 0), Litex.In a Litex.C :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact litex_param_fact_1

noncomputable def obj_61 : Litex.Object :=
  Litex.C

noncomputable def obj_62 (a : Litex.Object) : Litex.Object :=
  a

noncomputable def obj_63 (b : Litex.Object) : Litex.Object :=
  b

noncomputable def obj_65 (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (litex_domain_fact_1 : b ≠ 0) : Litex.Object :=
  (Litex.div (obj_62 a) (obj_63 b) (well_defined_fact_46 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) (well_defined_fact_47 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) (well_defined_fact_45 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1))

noncomputable def obj_66 (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (litex_domain_fact_1 : b ≠ 0) : Litex.Object :=
  (Litex.add (obj_65 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) (obj_62 a) (well_defined_fact_48 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) (well_defined_fact_49 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1))

theorem fact52 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (litex_domain_fact_1 : b ≠ 0), (obj_66 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) = (obj_66 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact rfl

theorem well_defined_fact_60 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (litex_domain_fact_1 : b ≠ 0), b ≠ 0 :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact litex_domain_fact_1

theorem well_defined_fact_61 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (litex_domain_fact_1 : b ≠ 0), Litex.In a Litex.R :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact litex_param_fact_1

theorem well_defined_fact_62 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (litex_domain_fact_1 : b ≠ 0), Litex.In a Litex.C :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact (Litex.BuiltinRules.realInComplex (litex_param_fact_1))

theorem well_defined_fact_63 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (litex_domain_fact_1 : b ≠ 0), Litex.In b Litex.R :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact litex_param_fact_2

theorem well_defined_fact_64 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (litex_domain_fact_1 : b ≠ 0), Litex.In b Litex.C :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact (Litex.BuiltinRules.realInComplex (litex_param_fact_2))

noncomputable def obj_80 (a : Litex.Object) : Litex.Object :=
  a

noncomputable def obj_81 (b : Litex.Object) : Litex.Object :=
  b

noncomputable def obj_83 : Litex.Object :=
  Litex.C

noncomputable def obj_84 (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (litex_domain_fact_1 : b ≠ 0) : Litex.Object :=
  (Litex.div (obj_80 a) (obj_81 b) (well_defined_fact_62 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) (well_defined_fact_64 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) (well_defined_fact_60 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1))

theorem fact65 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (litex_domain_fact_1 : b ≠ 0), Litex.In (obj_84 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) Litex.R :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact (Litex.BuiltinRules.realDivClosure ((well_defined_fact_62 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1)) ((well_defined_fact_64 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1)) ((well_defined_fact_60 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1)) (litex_param_fact_1) (litex_param_fact_2))
```
<!-- END ACTUAL GENERATED LEAN: proof_carrying_arithmetic -->

Required generated shape:

```lean
noncomputable def obj_<quotient> ... :=
  Litex.div obj_<a> obj_<b>
    well_defined_fact_<a_in_C>
    well_defined_fact_<b_in_C>
    well_defined_fact_<b_ne_zero>

theorem well_defined_fact_<quotient_in_C> ... :
    Litex.In obj_<quotient> Litex.C := by
  exact Litex.BuiltinRules.complexDivClosure ...

noncomputable def obj_<outer> ... :=
  Litex.add obj_<quotient> obj_<a>
    well_defined_fact_<quotient_in_C> ...
```

Boundary: deleting, duplicating, misindexing, or retargeting any of the three
division requirements fails before Lean emission. The shared ABI also makes
`Litex.div a b ha hb` ill-typed because the nonzero proof is missing.

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
import Litex.BuiltinRules

example : Litex.abiVersion = 8 := rfl

theorem fact16 : ∀ (x : Litex.Object) (litex_param_fact_1 : Litex.In x Litex.RPos), Litex.Lt 0 x :=
by
  intro x litex_param_fact_1
  have litex_inferred_fact_1 : Litex.Lt 0 x := by
    exact (Litex.BuiltinRules.positiveRealMembership litex_param_fact_1)
  exact litex_inferred_fact_1
```
<!-- END ACTUAL GENERATED LEAN: inferred_forall_premise -->

Required generated shape:

```lean
theorem fact... :
    ∀ (x : Litex.Object) (_ : Litex.In x Litex.RPos), Litex.Lt 0 x := by
  intro x litex_param_fact_1
  have litex_inferred_fact_1 : Litex.Lt 0 x := by
    exact Litex.BuiltinRules.positiveRealMembership litex_param_fact_1
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
import Litex.BuiltinRules

example : Litex.abiVersion = 8 := rfl

theorem well_defined_fact_2 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.IsSet a) (b : Litex.Object) (litex_param_fact_2 : Litex.IsSet b) (litex_domain_fact_1 : a ≠ b), a ≠ b :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact litex_domain_fact_1

noncomputable def obj_4 (a : Litex.Object) : Litex.Object :=
  a

noncomputable def obj_5 (b : Litex.Object) : Litex.Object :=
  b

noncomputable def obj_6 (a : Litex.Object) (litex_param_fact_1 : Litex.IsSet a) (b : Litex.Object) (litex_param_fact_2 : Litex.IsSet b) (litex_domain_fact_1 : a ≠ b) : Litex.Object :=
  (Litex.listSet [(obj_4 a), (obj_5 b)] (by
  apply List.Pairwise.cons
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst x
    exact (well_defined_fact_2 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1)
  · apply List.Pairwise.cons
    · intro x hx
      simp only [List.not_mem_nil] at hx
    · exact List.Pairwise.nil))

theorem fact13 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.IsSet a) (b : Litex.Object) (litex_param_fact_2 : Litex.IsSet b) (litex_domain_fact_1 : a ≠ b), (obj_6 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) = (obj_6 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact rfl

theorem well_defined_fact_7 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.IsSet a) (b : Litex.Object) (litex_param_fact_2 : Litex.IsSet b) (c : Litex.Object) (litex_param_fact_3 : Litex.IsSet c) (litex_domain_fact_1 : a ≠ b) (litex_domain_fact_2 : a ≠ c) (litex_domain_fact_3 : b ≠ c), a ≠ b :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3 litex_domain_fact_1 litex_domain_fact_2 litex_domain_fact_3
  exact litex_domain_fact_1

theorem well_defined_fact_8 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.IsSet a) (b : Litex.Object) (litex_param_fact_2 : Litex.IsSet b) (c : Litex.Object) (litex_param_fact_3 : Litex.IsSet c) (litex_domain_fact_1 : a ≠ b) (litex_domain_fact_2 : a ≠ c) (litex_domain_fact_3 : b ≠ c), a ≠ c :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3 litex_domain_fact_1 litex_domain_fact_2 litex_domain_fact_3
  exact litex_domain_fact_2

theorem well_defined_fact_9 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.IsSet a) (b : Litex.Object) (litex_param_fact_2 : Litex.IsSet b) (c : Litex.Object) (litex_param_fact_3 : Litex.IsSet c) (litex_domain_fact_1 : a ≠ b) (litex_domain_fact_2 : a ≠ c) (litex_domain_fact_3 : b ≠ c), b ≠ c :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3 litex_domain_fact_1 litex_domain_fact_2 litex_domain_fact_3
  exact litex_domain_fact_3

noncomputable def obj_14 (a : Litex.Object) : Litex.Object :=
  a

noncomputable def obj_15 (b : Litex.Object) : Litex.Object :=
  b

noncomputable def obj_16 (c : Litex.Object) : Litex.Object :=
  c

noncomputable def obj_17 (a : Litex.Object) (litex_param_fact_1 : Litex.IsSet a) (b : Litex.Object) (litex_param_fact_2 : Litex.IsSet b) (c : Litex.Object) (litex_param_fact_3 : Litex.IsSet c) (litex_domain_fact_1 : a ≠ b) (litex_domain_fact_2 : a ≠ c) (litex_domain_fact_3 : b ≠ c) : Litex.Object :=
  (Litex.listSet [(obj_14 a), (obj_15 b), (obj_16 c)] (by
  apply List.Pairwise.cons
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (hx_0 | hx_1)
    · subst x
      exact (well_defined_fact_7 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3 litex_domain_fact_1 litex_domain_fact_2 litex_domain_fact_3)
    · subst x
      exact (well_defined_fact_8 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3 litex_domain_fact_1 litex_domain_fact_2 litex_domain_fact_3)
  · apply List.Pairwise.cons
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      subst x
      exact (well_defined_fact_9 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3 litex_domain_fact_1 litex_domain_fact_2 litex_domain_fact_3)
    · apply List.Pairwise.cons
      · intro x hx
        simp only [List.not_mem_nil] at hx
      · exact List.Pairwise.nil))

theorem fact35 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.IsSet a) (b : Litex.Object) (litex_param_fact_2 : Litex.IsSet b) (c : Litex.Object) (litex_param_fact_3 : Litex.IsSet c) (litex_domain_fact_1 : a ≠ b) (litex_domain_fact_2 : a ≠ c) (litex_domain_fact_3 : b ≠ c), (obj_17 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3 litex_domain_fact_1 litex_domain_fact_2 litex_domain_fact_3) = (obj_17 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3 litex_domain_fact_1 litex_domain_fact_2 litex_domain_fact_3) :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3 litex_domain_fact_1 litex_domain_fact_2 litex_domain_fact_3
  exact rfl
```
<!-- END ACTUAL GENERATED LEAN: proof_carrying_list_set -->

Required generated shape:

```lean
noncomputable def obj_<set> ... : Litex.Object :=
  Litex.listSet [obj_<a>, obj_<b>, obj_<c>] (by
    apply List.Pairwise.cons
    · ...
      exact well_defined_fact_<a_ne_b>
    · ...)
```

The source-order matrix is exact: `(0,1)` cites `a ≠ b`, `(0,2)` cites
`a ≠ c`, and `(1,2)` cites `b ≠ c`. Missing, duplicated, reversed,
out-of-range, or retargeted roles fail before Lean emission. The shared ABI
also rejects `Litex.listSet [a]` when its WD proof argument is omitted.

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
import Litex.BuiltinRules

example : Litex.abiVersion = 8 := rfl

noncomputable def x : Litex.Object := Classical.choose (Litex.BuiltinRules.realSetNonempty)

theorem fact3 : Litex.In x Litex.R := by
  unfold x
  exact Classical.choose_spec (Litex.BuiltinRules.realSetNonempty)
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
import Litex.BuiltinRules

example : Litex.abiVersion = 8 := rfl

theorem fact8 : ∃ (x : Litex.Object), Litex.In x Litex.R ∧ x = 1 := by
  exact (by
  have litex_exist_step_1 : (1 : Litex.Object) = 1 := by
    exact rfl
  exact ⟨1, (Litex.BuiltinRules.numeralInR 1), (litex_exist_step_1)⟩)

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
import Litex.BuiltinRules

example : Litex.abiVersion = 8 := rfl

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
import Litex.BuiltinRules

example : Litex.abiVersion = 8 := rfl

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
import Litex.BuiltinRules

example : Litex.abiVersion = 8 := rfl

theorem fact1 : Litex.pi = Litex.pi := by
  exact rfl

theorem fact11 : ∀ (A : Litex.Object) (litex_param_fact_1 : Litex.IsSet A) (B : Litex.Object) (litex_param_fact_2 : Litex.IsSet B), (Litex.union A B) = (Litex.union A B) :=
by
  intro A litex_param_fact_1 B litex_param_fact_2
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
import Litex.BuiltinRules

example : Litex.abiVersion = 8 := rfl

theorem well_defined_fact_4 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (litex_domain_fact_1 : b ≠ 0), b ≠ 0 :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact litex_domain_fact_1

theorem well_defined_fact_5 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (litex_domain_fact_1 : b ≠ 0), Litex.In a Litex.C :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact litex_param_fact_1

theorem well_defined_fact_6 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (litex_domain_fact_1 : b ≠ 0), Litex.In b Litex.C :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact litex_param_fact_2

noncomputable def obj_7 (a : Litex.Object) : Litex.Object :=
  a

noncomputable def obj_8 (b : Litex.Object) : Litex.Object :=
  b

noncomputable def obj_10 (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (litex_domain_fact_1 : b ≠ 0) : Litex.Object :=
  (Litex.div (obj_7 a) (obj_8 b) (well_defined_fact_5 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) (well_defined_fact_6 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) (well_defined_fact_4 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1))

theorem fact13 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (litex_domain_fact_1 : b ≠ 0), (obj_10 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) = (obj_10 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact rfl

theorem well_defined_fact_15 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (litex_domain_fact_1 : b ≠ 0), b ≠ 0 :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact litex_domain_fact_1

theorem well_defined_fact_16 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (litex_domain_fact_1 : b ≠ 0), Litex.In a Litex.R :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact litex_param_fact_1

theorem well_defined_fact_17 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (litex_domain_fact_1 : b ≠ 0), Litex.In a Litex.C :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact (Litex.BuiltinRules.realInComplex (litex_param_fact_1))

theorem well_defined_fact_18 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (litex_domain_fact_1 : b ≠ 0), Litex.In b Litex.R :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact litex_param_fact_2

theorem well_defined_fact_19 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (litex_domain_fact_1 : b ≠ 0), Litex.In b Litex.C :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact (Litex.BuiltinRules.realInComplex (litex_param_fact_2))

noncomputable def obj_23 (a : Litex.Object) : Litex.Object :=
  a

noncomputable def obj_24 (b : Litex.Object) : Litex.Object :=
  b

noncomputable def obj_26 : Litex.Object :=
  Litex.C

noncomputable def obj_27 (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (litex_domain_fact_1 : b ≠ 0) : Litex.Object :=
  (Litex.div (obj_23 a) (obj_24 b) (well_defined_fact_17 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) (well_defined_fact_19 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) (well_defined_fact_15 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1))

theorem fact26 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (litex_domain_fact_1 : b ≠ 0), Litex.In (obj_27 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) Litex.R :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact (Litex.BuiltinRules.realDivClosure ((well_defined_fact_17 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1)) ((well_defined_fact_19 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1)) ((well_defined_fact_15 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1)) (litex_param_fact_1) (litex_param_fact_2))
```
<!-- END ACTUAL GENERATED LEAN: proof_carrying_division -->

`Litex.div` consumes two `C` memberships and the exact nonzero proof; none of
the three slots can be deleted, moved, or reconstructed by target search.

```lean
noncomputable def obj_<quotient> :=
  Litex.div a b fact_<a_in_C> fact_<b_in_C> fact_<b_ne_zero>
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
import Litex.BuiltinRules

example : Litex.abiVersion = 8 := rfl

noncomputable def S : Litex.Object := (Litex.setBuilder Litex.R (fun litex_set_builder_2 => litex_set_builder_2 = litex_set_builder_2))

theorem fact4 : Litex.IsSet S := by
  simpa only [S] using (Litex.BuiltinRules.objectIsSet (Litex.setBuilder Litex.R (fun litex_set_builder_2 => litex_set_builder_2 = litex_set_builder_2)))

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
`well_defined_fact_N`/`obj_N` body DAG, range proof, membership, definition,
and exact replay. `inc` exercises proof-carrying addition; `reciprocal` passes
its retained domain fact directly to division.

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
import Litex.BuiltinRules

example : Litex.abiVersion = 8 := rfl

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
  Litex.functionObject litex_id_spec litex_id_body litex_id_closed

noncomputable def litex_id : Litex.Object := litex_id_implementation

theorem fact5 : Litex.In litex_id (Litex.FnSet ({ arity := 1, requirements := fun litex_function_args => ∃ litex_function_premise_1 : Litex.In (Litex.arg litex_function_args 0) Litex.R, True, range := fun litex_function_args litex_function_length litex_function_requirements => Litex.R } : Litex.FnSpec)) := by
  simpa only [litex_id, litex_id_implementation, litex_id_spec] using
    (Litex.functionObjectInFnSet litex_id_spec litex_id_body litex_id_closed)

theorem fact6 : litex_id = litex_id_implementation := by
  rfl

theorem well_defined_fact_2 : Litex.In 1 Litex.R :=
by
  exact Litex.BuiltinRules.numeralInR 1

noncomputable def obj_13 : Litex.Object :=
  1

noncomputable def obj_14 : Litex.Object :=
  Litex.R

theorem obj_15_applicable : Litex.Applicable litex_id [obj_13] :=
by
  exact Litex.fnSetApplicable fact5 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In (obj_13) Litex.R, True
  exact Exists.intro (well_defined_fact_2) (True.intro))

noncomputable def obj_15 : Litex.Object :=
  litex_id [obj_13] (obj_15_applicable)

theorem obj_15_result : Litex.In obj_15 Litex.R :=
by
  simpa [obj_15] using (Litex.fnSetResult fact5 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In (obj_13) Litex.R, True
  exact Exists.intro (well_defined_fact_2) (True.intro)))

theorem fact7 : obj_15 = 1 := by
  exact (by
  change (litex_id [1] (obj_15_applicable)) = 1
  simp only [fact6, litex_id_implementation, litex_id_body, obj_13, obj_14, obj_15, Litex.functionObject_apply, Litex.arg, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil])

theorem well_defined_fact_8 : ∀ (litex_function_arg_1 : Litex.Object) (litex_function_premise_1 : Litex.In litex_function_arg_1 Litex.R), Litex.In litex_function_arg_1 Litex.R :=
by
  intro litex_function_arg_1 litex_function_premise_1
  exact litex_function_premise_1

theorem well_defined_fact_9 : ∀ (litex_function_arg_1 : Litex.Object) (litex_function_premise_1 : Litex.In litex_function_arg_1 Litex.R), Litex.In litex_function_arg_1 Litex.C :=
by
  intro litex_function_arg_1 litex_function_premise_1
  exact (Litex.BuiltinRules.realInComplex (litex_function_premise_1))

theorem well_defined_fact_10 : ∀ (litex_function_arg_1 : Litex.Object) (litex_function_premise_1 : Litex.In litex_function_arg_1 Litex.R), Litex.In 1 Litex.C :=
by
  intro litex_function_arg_1 litex_function_premise_1
  exact Litex.BuiltinRules.numeralInC 1

noncomputable def obj_22 (litex_function_arg_1 : Litex.Object) : Litex.Object :=
  litex_function_arg_1

noncomputable def obj_23 : Litex.Object :=
  Litex.C

noncomputable def obj_24 (litex_function_arg_1 : Litex.Object) (litex_function_premise_1 : Litex.In litex_function_arg_1 Litex.R) : Litex.Object :=
  (Litex.add (obj_22 litex_function_arg_1) obj_13 (well_defined_fact_9 litex_function_arg_1 litex_function_premise_1) (well_defined_fact_10 litex_function_arg_1 litex_function_premise_1))

noncomputable def inc_spec : Litex.FnSpec :=
  ({ arity := 1, requirements := fun litex_function_args => ∃ litex_function_premise_1 : Litex.In (Litex.arg litex_function_args 0) Litex.R, True, range := fun litex_function_args litex_function_length litex_function_requirements => Litex.R } : Litex.FnSpec)

noncomputable def inc_body
    (litex_function_args : List Litex.Object)
    (litex_function_length : litex_function_args.length = inc_spec.arity)
    (litex_function_requirements : inc_spec.requirements litex_function_args) : Litex.Object :=
  (obj_24 ((Litex.arg litex_function_args 0)) (Exists.choose (litex_function_requirements)))

theorem inc_closed :
    ∀ litex_function_args litex_function_length litex_function_requirements,
      Litex.In
        (inc_body litex_function_args litex_function_length litex_function_requirements)
        (inc_spec.range litex_function_args litex_function_length litex_function_requirements) := by
  intro litex_function_args litex_function_length litex_function_requirements
  change Litex.In (obj_24 ((Litex.arg litex_function_args 0)) (Exists.choose (litex_function_requirements))) Litex.R
  exact (Litex.BuiltinRules.realAddClosure ((well_defined_fact_9 ((Litex.arg litex_function_args 0)) (Exists.choose (litex_function_requirements)))) ((well_defined_fact_10 ((Litex.arg litex_function_args 0)) (Exists.choose (litex_function_requirements)))) (Exists.choose (litex_function_requirements)) (Litex.BuiltinRules.numeralInR 1))

noncomputable def inc_implementation : Litex.Object :=
  Litex.functionObject inc_spec inc_body inc_closed

noncomputable def inc : Litex.Object := inc_implementation

theorem fact12 : Litex.In inc (Litex.FnSet ({ arity := 1, requirements := fun litex_function_args => ∃ litex_function_premise_1 : Litex.In (Litex.arg litex_function_args 0) Litex.R, True, range := fun litex_function_args litex_function_length litex_function_requirements => Litex.R } : Litex.FnSpec)) := by
  simpa only [inc, inc_implementation, inc_spec] using
    (Litex.functionObjectInFnSet inc_spec inc_body inc_closed)

theorem fact13 : inc = inc_implementation := by
  rfl

theorem well_defined_fact_11 : Litex.In 1 Litex.R :=
by
  exact Litex.BuiltinRules.numeralInR 1

theorem obj_28_applicable : Litex.Applicable inc [obj_13] :=
by
  exact Litex.fnSetApplicable fact12 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In (obj_13) Litex.R, True
  exact Exists.intro (well_defined_fact_11) (True.intro))

noncomputable def obj_28 : Litex.Object :=
  inc [obj_13] (obj_28_applicable)

theorem obj_28_result : Litex.In obj_28 Litex.R :=
by
  simpa [obj_28] using (Litex.fnSetResult fact12 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In (obj_13) Litex.R, True
  exact Exists.intro (well_defined_fact_11) (True.intro)))

theorem well_defined_fact_12 : Litex.In 1 Litex.C :=
by
  exact Litex.BuiltinRules.numeralInC 1

noncomputable def obj_29 : Litex.Object :=
  Litex.C

noncomputable def obj_30 : Litex.Object :=
  (Litex.add obj_13 obj_13 well_defined_fact_12 well_defined_fact_12)

theorem fact14 : obj_28 = obj_30 := by
  exact (by
  change (inc [1] (obj_28_applicable)) = obj_30
  simp only [fact13, inc_implementation, inc_body, obj_13, obj_14, obj_22, obj_23, obj_24, obj_28, obj_29, obj_30, Litex.functionObject_apply, Litex.arg, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil])

theorem well_defined_fact_19 : ∀ (litex_function_arg_1 : Litex.Object) (litex_function_premise_1 : Litex.In litex_function_arg_1 Litex.R) (litex_function_premise_2 : litex_function_arg_1 ≠ 0), litex_function_arg_1 ≠ 0 :=
by
  intro litex_function_arg_1 litex_function_premise_1 litex_function_premise_2
  exact litex_function_premise_2

theorem well_defined_fact_20 : ∀ (litex_function_arg_1 : Litex.Object) (litex_function_premise_1 : Litex.In litex_function_arg_1 Litex.R) (litex_function_premise_2 : litex_function_arg_1 ≠ 0), Litex.In 1 Litex.C :=
by
  intro litex_function_arg_1 litex_function_premise_1 litex_function_premise_2
  exact Litex.BuiltinRules.numeralInC 1

theorem well_defined_fact_21 : ∀ (litex_function_arg_1 : Litex.Object) (litex_function_premise_1 : Litex.In litex_function_arg_1 Litex.R) (litex_function_premise_2 : litex_function_arg_1 ≠ 0), Litex.In litex_function_arg_1 Litex.R :=
by
  intro litex_function_arg_1 litex_function_premise_1 litex_function_premise_2
  exact litex_function_premise_1

theorem well_defined_fact_22 : ∀ (litex_function_arg_1 : Litex.Object) (litex_function_premise_1 : Litex.In litex_function_arg_1 Litex.R) (litex_function_premise_2 : litex_function_arg_1 ≠ 0), Litex.In litex_function_arg_1 Litex.C :=
by
  intro litex_function_arg_1 litex_function_premise_1 litex_function_premise_2
  exact (Litex.BuiltinRules.realInComplex (litex_function_premise_1))

noncomputable def obj_38 (litex_function_arg_1 : Litex.Object) : Litex.Object :=
  litex_function_arg_1

noncomputable def obj_39 (litex_function_arg_1 : Litex.Object) (litex_function_premise_1 : Litex.In litex_function_arg_1 Litex.R) (litex_function_premise_2 : litex_function_arg_1 ≠ 0) : Litex.Object :=
  (Litex.div obj_13 (obj_38 litex_function_arg_1) (well_defined_fact_20 litex_function_arg_1 litex_function_premise_1 litex_function_premise_2) (well_defined_fact_22 litex_function_arg_1 litex_function_premise_1 litex_function_premise_2) (well_defined_fact_19 litex_function_arg_1 litex_function_premise_1 litex_function_premise_2))

noncomputable def reciprocal_spec : Litex.FnSpec :=
  ({ arity := 1, requirements := fun litex_function_args => ∃ litex_function_premise_1 : Litex.In (Litex.arg litex_function_args 0) Litex.R, ∃ litex_function_premise_2 : (Litex.arg litex_function_args 0) ≠ 0, True, range := fun litex_function_args litex_function_length litex_function_requirements => Litex.R } : Litex.FnSpec)

noncomputable def reciprocal_body
    (litex_function_args : List Litex.Object)
    (litex_function_length : litex_function_args.length = reciprocal_spec.arity)
    (litex_function_requirements : reciprocal_spec.requirements litex_function_args) : Litex.Object :=
  (obj_39 ((Litex.arg litex_function_args 0)) (Exists.choose (litex_function_requirements)) (Exists.choose (Exists.choose_spec (litex_function_requirements))))

theorem reciprocal_closed :
    ∀ litex_function_args litex_function_length litex_function_requirements,
      Litex.In
        (reciprocal_body litex_function_args litex_function_length litex_function_requirements)
        (reciprocal_spec.range litex_function_args litex_function_length litex_function_requirements) := by
  intro litex_function_args litex_function_length litex_function_requirements
  change Litex.In (obj_39 ((Litex.arg litex_function_args 0)) (Exists.choose (litex_function_requirements)) (Exists.choose (Exists.choose_spec (litex_function_requirements)))) Litex.R
  exact (Litex.BuiltinRules.realDivClosure ((well_defined_fact_20 ((Litex.arg litex_function_args 0)) (Exists.choose (litex_function_requirements)) (Exists.choose (Exists.choose_spec (litex_function_requirements))))) ((well_defined_fact_22 ((Litex.arg litex_function_args 0)) (Exists.choose (litex_function_requirements)) (Exists.choose (Exists.choose_spec (litex_function_requirements))))) ((well_defined_fact_19 ((Litex.arg litex_function_args 0)) (Exists.choose (litex_function_requirements)) (Exists.choose (Exists.choose_spec (litex_function_requirements))))) (Litex.BuiltinRules.numeralInR 1) (Exists.choose (litex_function_requirements)))

noncomputable def reciprocal_implementation : Litex.Object :=
  Litex.functionObject reciprocal_spec reciprocal_body reciprocal_closed

noncomputable def reciprocal : Litex.Object := reciprocal_implementation

theorem fact23 : Litex.In reciprocal (Litex.FnSet ({ arity := 1, requirements := fun litex_function_args => ∃ litex_function_premise_1 : Litex.In (Litex.arg litex_function_args 0) Litex.R, ∃ litex_function_premise_2 : (Litex.arg litex_function_args 0) ≠ 0, True, range := fun litex_function_args litex_function_length litex_function_requirements => Litex.R } : Litex.FnSpec)) := by
  simpa only [reciprocal, reciprocal_implementation, reciprocal_spec] using
    (Litex.functionObjectInFnSet reciprocal_spec reciprocal_body reciprocal_closed)

theorem fact24 : reciprocal = reciprocal_implementation := by
  rfl

theorem well_defined_fact_28 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (litex_domain_fact_1 : a ≠ 0), Litex.In a Litex.R :=
by
  intro a litex_param_fact_1 litex_domain_fact_1
  exact litex_param_fact_1

theorem well_defined_fact_29 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (litex_domain_fact_1 : a ≠ 0), a ≠ 0 :=
by
  intro a litex_param_fact_1 litex_domain_fact_1
  exact litex_domain_fact_1

noncomputable def obj_48 (a : Litex.Object) : Litex.Object :=
  a

theorem obj_50_applicable : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (litex_domain_fact_1 : a ≠ 0), Litex.Applicable reciprocal [(obj_48 a)] :=
by
  intro a litex_param_fact_1 litex_domain_fact_1
  exact Litex.fnSetApplicable fact23 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In ((obj_48 a)) Litex.R, ∃ litex_application_requirement_2 : ((obj_48 a)) ≠ 0, True
  exact Exists.intro ((well_defined_fact_28 a litex_param_fact_1 litex_domain_fact_1)) (Exists.intro ((well_defined_fact_29 a litex_param_fact_1 litex_domain_fact_1)) (True.intro)))

noncomputable def obj_50 (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (litex_domain_fact_1 : a ≠ 0) : Litex.Object :=
  reciprocal [(obj_48 a)] ((obj_50_applicable a litex_param_fact_1 litex_domain_fact_1))

theorem obj_50_result : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (litex_domain_fact_1 : a ≠ 0), Litex.In (obj_50 a litex_param_fact_1 litex_domain_fact_1) Litex.R :=
by
  intro a litex_param_fact_1 litex_domain_fact_1
  simpa [obj_50] using (Litex.fnSetResult fact23 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In ((obj_48 a)) Litex.R, ∃ litex_application_requirement_2 : ((obj_48 a)) ≠ 0, True
  exact Exists.intro ((well_defined_fact_28 a litex_param_fact_1 litex_domain_fact_1)) (Exists.intro ((well_defined_fact_29 a litex_param_fact_1 litex_domain_fact_1)) (True.intro))))

theorem well_defined_fact_30 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (litex_domain_fact_1 : a ≠ 0), a ≠ 0 :=
by
  intro a litex_param_fact_1 litex_domain_fact_1
  exact litex_domain_fact_1

theorem well_defined_fact_31 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (litex_domain_fact_1 : a ≠ 0), Litex.In 1 Litex.C :=
by
  intro a litex_param_fact_1 litex_domain_fact_1
  exact Litex.BuiltinRules.numeralInC 1

theorem well_defined_fact_32 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (litex_domain_fact_1 : a ≠ 0), Litex.In a Litex.C :=
by
  intro a litex_param_fact_1 litex_domain_fact_1
  exact (Litex.BuiltinRules.realInComplex (litex_param_fact_1))

noncomputable def obj_51 (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (litex_domain_fact_1 : a ≠ 0) : Litex.Object :=
  (Litex.div obj_13 (obj_48 a) (well_defined_fact_31 a litex_param_fact_1 litex_domain_fact_1) (well_defined_fact_32 a litex_param_fact_1 litex_domain_fact_1) (well_defined_fact_30 a litex_param_fact_1 litex_domain_fact_1))

theorem fact34 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (litex_domain_fact_1 : a ≠ 0), (obj_50 a litex_param_fact_1 litex_domain_fact_1) = (obj_51 a litex_param_fact_1 litex_domain_fact_1) :=
by
  intro a litex_param_fact_1 litex_domain_fact_1
  exact (by
  change (reciprocal [a] ((obj_50_applicable a litex_param_fact_1 litex_domain_fact_1))) = (obj_51 a litex_param_fact_1 litex_domain_fact_1)
  simp only [fact24, reciprocal_implementation, reciprocal_body, obj_13, obj_29, obj_38, obj_39, obj_48, obj_50, obj_51, Litex.functionObject_apply, Litex.arg, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil])
```
<!-- END ACTUAL GENERATED LEAN: named_function -->

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
noncomputable def id := Litex.functionObject id_spec id_body id_closed
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
import Litex.BuiltinRules

example : Litex.abiVersion = 8 := rfl

theorem q_dimension_positive : Litex.In 2 Litex.NPos := by
  exact (Litex.BuiltinRules.numeralInNPos 2 (by norm_num))

theorem q_dimension_at_least_two : Litex.Le 2 2 := by
  exact (by
  exact (Litex.BuiltinRules.numeralLe 2 2).2 (by norm_num))

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

theorem fact14 : ∀ (_binder_2 : Litex.Object) (litex_nested_param_fact_2 : Litex.In _binder_2 (Litex.closedRange 1 2)), (Litex.atIndex q _binder_2) = 0 :=
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
import Litex.BuiltinRules

example : Litex.abiVersion = 8 := rfl

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
  Litex.functionObject litex_id_spec litex_id_body litex_id_closed

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
  exact ⟨1, (Litex.BuiltinRules.numeralInR 1), (litex_exist_step_1)⟩)

noncomputable def y : Litex.Object := Classical.choose (fact14)

theorem fact19 : Litex.In y Litex.R := by
  unfold y
  exact (Classical.choose_spec (fact14)).1

theorem fact20 : y = 1 := by
  unfold y
  exact (Classical.choose_spec (fact14)).2

theorem well_defined_fact_2 : Litex.In y Litex.R :=
by
  exact fact19

noncomputable def obj_30 : Litex.Object :=
  y

theorem obj_33_applicable : Litex.Applicable litex_id [obj_30] :=
by
  exact Litex.fnSetApplicable fact5 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In (obj_30) Litex.R, True
  exact Exists.intro (well_defined_fact_2) (True.intro))

noncomputable def obj_33 : Litex.Object :=
  litex_id [obj_30] (obj_33_applicable)

theorem obj_33_result : Litex.In obj_33 Litex.R :=
by
  simpa [obj_33] using (Litex.fnSetResult fact5 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In (obj_30) Litex.R, True
  exact Exists.intro (well_defined_fact_2) (True.intro)))

theorem fact21 : obj_33 = y := by
  exact (by
  change (litex_id [y] (obj_33_applicable)) = y
  simp only [fact6, litex_id_implementation, litex_id_body, obj_30, obj_33, Litex.functionObject_apply, Litex.arg, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil])

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
  Litex.functionObject into_builder_spec into_builder_body into_builder_closed

noncomputable def into_builder : Litex.Object := into_builder_implementation

theorem fact40 : Litex.In into_builder (Litex.FnSet ({ arity := 1, requirements := fun litex_function_args => ∃ litex_function_premise_1 : Litex.In (Litex.arg litex_function_args 0) Litex.R, True, range := fun litex_function_args litex_function_length litex_function_requirements => (Litex.setBuilder Litex.R (fun litex_set_builder_9 => litex_set_builder_9 = litex_set_builder_9)) } : Litex.FnSpec)) := by
  simpa only [into_builder, into_builder_implementation, into_builder_spec] using
    (Litex.functionObjectInFnSet into_builder_spec into_builder_body into_builder_closed)

theorem fact41 : into_builder = into_builder_implementation := by
  rfl

theorem well_defined_fact_6 : Litex.In 1 Litex.R :=
by
  exact Litex.BuiltinRules.numeralInR 1

noncomputable def obj_31 : Litex.Object :=
  Litex.R

noncomputable def obj_32 : Litex.Object :=
  1

theorem obj_52_applicable : Litex.Applicable into_builder [obj_32] :=
by
  exact Litex.fnSetApplicable fact40 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In (obj_32) Litex.R, True
  exact Exists.intro (well_defined_fact_6) (True.intro))

noncomputable def obj_52 : Litex.Object :=
  into_builder [obj_32] (obj_52_applicable)

theorem obj_52_result : Litex.In obj_52 (Litex.setBuilder Litex.R (fun litex_set_builder_9 => litex_set_builder_9 = litex_set_builder_9)) :=
by
  simpa [obj_52] using (Litex.fnSetResult fact40 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In (obj_32) Litex.R, True
  exact Exists.intro (well_defined_fact_6) (True.intro)))

theorem fact42 : obj_52 = 1 := by
  exact (by
  change (into_builder [1] (obj_52_applicable)) = 1
  simp only [fact41, into_builder_implementation, into_builder_body, obj_31, obj_32, obj_52, Litex.functionObject_apply, Litex.arg, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil])
```
<!-- END ACTUAL GENERATED LEAN: statement_object_interactions -->

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
import Litex.BuiltinRules

example : Litex.abiVersion = 8 := rfl

theorem well_defined_fact_3 : ∀ (litex_wd_scope_3_arg_1 : Litex.Object) (litex_wd_scope_3_premise_1 : Litex.In litex_wd_scope_3_arg_1 Litex.R), Litex.In litex_wd_scope_3_arg_1 Litex.R :=
by
  intro litex_wd_scope_3_arg_1 litex_wd_scope_3_premise_1
  exact litex_wd_scope_3_premise_1

theorem well_defined_fact_4 : ∀ (litex_wd_scope_4_arg_1 : Litex.Object) (litex_wd_scope_4_premise_1 : Litex.In litex_wd_scope_4_arg_1 Litex.R), Litex.In litex_wd_scope_4_arg_1 Litex.R :=
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
  exact (well_defined_fact_3 (Litex.arg litex_obj_9_args 0) (Exists.choose (litex_obj_9_requirements)))

noncomputable def obj_9 : Litex.Object :=
  Litex.functionObject obj_9_spec obj_9_body obj_9_closed

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
  exact (well_defined_fact_4 (Litex.arg litex_obj_12_args 0) (Exists.choose (litex_obj_12_requirements)))

noncomputable def obj_12 : Litex.Object :=
  Litex.functionObject obj_12_spec obj_12_body obj_12_closed

theorem obj_12_in_fn_set :
    Litex.In obj_12 (Litex.FnSet obj_12_spec) := by
  unfold obj_12
  exact Litex.functionObjectInFnSet obj_12_spec obj_12_body obj_12_closed

theorem fact7 : obj_9 = obj_12 := by
  exact rfl

theorem well_defined_fact_11 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (litex_wd_scope_9_arg_1 : Litex.Object) (litex_wd_scope_9_premise_1 : Litex.In litex_wd_scope_9_arg_1 Litex.R), Litex.In litex_wd_scope_9_arg_1 Litex.R :=
by
  intro a litex_param_fact_1 litex_wd_scope_9_arg_1 litex_wd_scope_9_premise_1
  exact litex_wd_scope_9_premise_1

theorem well_defined_fact_12 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R), Litex.In a Litex.R :=
by
  intro a litex_param_fact_1
  exact litex_param_fact_1

noncomputable def obj_27 : Litex.Object :=
  Litex.R

noncomputable def obj_28 (a : Litex.Object) : Litex.Object :=
  a

noncomputable def obj_29 (litex_wd_scope_9_arg_1 : Litex.Object) : Litex.Object :=
  litex_wd_scope_9_arg_1

noncomputable def obj_30_spec (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) : Litex.FnSpec :=
  ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec)

noncomputable def obj_30_body (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (litex_obj_30_args : List Litex.Object) (_litex_length : litex_obj_30_args.length = ((obj_30_spec a litex_param_fact_1)).arity) (_litex_requirements : ((obj_30_spec a litex_param_fact_1)).requirements litex_obj_30_args) : Litex.Object :=
  (obj_29 (Litex.arg litex_obj_30_args 0))

theorem obj_30_closed (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) :
    ∀ (litex_obj_30_args : List Litex.Object)
      (litex_obj_30_length : litex_obj_30_args.length = ((obj_30_spec a litex_param_fact_1)).arity)
      (litex_obj_30_requirements : ((obj_30_spec a litex_param_fact_1)).requirements litex_obj_30_args),
      Litex.In ((obj_30_body a litex_param_fact_1) litex_obj_30_args litex_obj_30_length litex_obj_30_requirements) (((obj_30_spec a litex_param_fact_1)).range litex_obj_30_args litex_obj_30_length litex_obj_30_requirements) :=
by
  intro litex_obj_30_args litex_obj_30_length litex_obj_30_requirements
  change Litex.In (Litex.arg litex_obj_30_args 0) Litex.R
  exact (well_defined_fact_11 (a) (litex_param_fact_1) (Litex.arg litex_obj_30_args 0) (Exists.choose (litex_obj_30_requirements)))

noncomputable def obj_30 (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) : Litex.Object :=
  Litex.functionObject (obj_30_spec a litex_param_fact_1) (obj_30_body a litex_param_fact_1) (obj_30_closed a litex_param_fact_1)

theorem obj_30_in_fn_set (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) :
    Litex.In (obj_30 a litex_param_fact_1) (Litex.FnSet (obj_30_spec a litex_param_fact_1)) := by
  unfold obj_30
  exact Litex.functionObjectInFnSet (obj_30_spec a litex_param_fact_1) (obj_30_body a litex_param_fact_1) (obj_30_closed a litex_param_fact_1)

theorem obj_31_applicable : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R), Litex.Applicable (obj_30 a litex_param_fact_1) [(obj_28 a)] :=
by
  intro a litex_param_fact_1
  exact Litex.fnSetApplicable (obj_30_in_fn_set a litex_param_fact_1) rfl (by
  change ∃ litex_application_requirement_1 : Litex.In ((obj_28 a)) Litex.R, True
  exact Exists.intro ((well_defined_fact_12 a litex_param_fact_1)) (True.intro))

noncomputable def obj_31 (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) : Litex.Object :=
  (obj_30 a litex_param_fact_1) [(obj_28 a)] ((obj_31_applicable a litex_param_fact_1))

theorem obj_31_result : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R), Litex.In (obj_31 a litex_param_fact_1) Litex.R :=
by
  intro a litex_param_fact_1
  simpa [obj_31] using (Litex.fnSetResult (obj_30_in_fn_set a litex_param_fact_1) rfl (by
  change ∃ litex_application_requirement_1 : Litex.In ((obj_28 a)) Litex.R, True
  exact Exists.intro ((well_defined_fact_12 a litex_param_fact_1)) (True.intro)))

theorem well_defined_fact_13 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (litex_wd_scope_10_arg_1 : Litex.Object) (litex_wd_scope_10_premise_1 : Litex.In litex_wd_scope_10_arg_1 Litex.R), Litex.In litex_wd_scope_10_arg_1 Litex.R :=
by
  intro a litex_param_fact_1 litex_wd_scope_10_arg_1 litex_wd_scope_10_premise_1
  exact litex_wd_scope_10_premise_1

theorem well_defined_fact_14 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R), Litex.In a Litex.R :=
by
  intro a litex_param_fact_1
  exact litex_param_fact_1

noncomputable def obj_32 (litex_wd_scope_10_arg_1 : Litex.Object) : Litex.Object :=
  litex_wd_scope_10_arg_1

noncomputable def obj_33_spec (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) : Litex.FnSpec :=
  ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec)

noncomputable def obj_33_body (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (litex_obj_33_args : List Litex.Object) (_litex_length : litex_obj_33_args.length = ((obj_33_spec a litex_param_fact_1)).arity) (_litex_requirements : ((obj_33_spec a litex_param_fact_1)).requirements litex_obj_33_args) : Litex.Object :=
  (obj_32 (Litex.arg litex_obj_33_args 0))

theorem obj_33_closed (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) :
    ∀ (litex_obj_33_args : List Litex.Object)
      (litex_obj_33_length : litex_obj_33_args.length = ((obj_33_spec a litex_param_fact_1)).arity)
      (litex_obj_33_requirements : ((obj_33_spec a litex_param_fact_1)).requirements litex_obj_33_args),
      Litex.In ((obj_33_body a litex_param_fact_1) litex_obj_33_args litex_obj_33_length litex_obj_33_requirements) (((obj_33_spec a litex_param_fact_1)).range litex_obj_33_args litex_obj_33_length litex_obj_33_requirements) :=
by
  intro litex_obj_33_args litex_obj_33_length litex_obj_33_requirements
  change Litex.In (Litex.arg litex_obj_33_args 0) Litex.R
  exact (well_defined_fact_13 (a) (litex_param_fact_1) (Litex.arg litex_obj_33_args 0) (Exists.choose (litex_obj_33_requirements)))

noncomputable def obj_33 (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) : Litex.Object :=
  Litex.functionObject (obj_33_spec a litex_param_fact_1) (obj_33_body a litex_param_fact_1) (obj_33_closed a litex_param_fact_1)

theorem obj_33_in_fn_set (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) :
    Litex.In (obj_33 a litex_param_fact_1) (Litex.FnSet (obj_33_spec a litex_param_fact_1)) := by
  unfold obj_33
  exact Litex.functionObjectInFnSet (obj_33_spec a litex_param_fact_1) (obj_33_body a litex_param_fact_1) (obj_33_closed a litex_param_fact_1)

theorem obj_34_applicable : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R), Litex.Applicable (obj_33 a litex_param_fact_1) [(obj_28 a)] :=
by
  intro a litex_param_fact_1
  exact Litex.fnSetApplicable (obj_33_in_fn_set a litex_param_fact_1) rfl (by
  change ∃ litex_application_requirement_1 : Litex.In ((obj_28 a)) Litex.R, True
  exact Exists.intro ((well_defined_fact_14 a litex_param_fact_1)) (True.intro))

noncomputable def obj_34 (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) : Litex.Object :=
  (obj_33 a litex_param_fact_1) [(obj_28 a)] ((obj_34_applicable a litex_param_fact_1))

theorem obj_34_result : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R), Litex.In (obj_34 a litex_param_fact_1) Litex.R :=
by
  intro a litex_param_fact_1
  simpa [obj_34] using (Litex.fnSetResult (obj_33_in_fn_set a litex_param_fact_1) rfl (by
  change ∃ litex_application_requirement_1 : Litex.In ((obj_28 a)) Litex.R, True
  exact Exists.intro ((well_defined_fact_14 a litex_param_fact_1)) (True.intro)))

theorem fact20 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R), (obj_31 a litex_param_fact_1) = (obj_34 a litex_param_fact_1) :=
by
  intro a litex_param_fact_1
  exact rfl
```
<!-- END ACTUAL GENERATED LEAN: anonymous_function -->

Required generated shape:

```lean
noncomputable def anonymous_fn_<id> : Litex.Object :=
  Litex.functionObject anonymous_fn_<id>_spec anonymous_fn_<id>_body
    anonymous_fn_<id>_closed

theorem anonymous_fn_<id>_applicable :
    Litex.Applicable anonymous_fn_<id> [a] := by ...
```

Boundary: `fn(x R) N {x}` remains rejected because the body has no proof that
an arbitrary real parameter belongs to `N`.

## arithmetic_forall_wd

Nested universal facts, subtraction, and function applications retain the
well-definedness evidence selected for each source occurrence. The object `y`
stays in the universal object type while its real membership is passed to the
subtraction and application constructors.

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
import Litex.BuiltinRules

example : Litex.abiVersion = 8 := rfl

theorem well_defined_fact_8 : ∀ (f : Litex.Object) (litex_param_fact_1 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (y : Litex.Object) (litex_nested_param_fact_2 : Litex.In y Litex.R), Litex.In y Litex.R :=
by
  intro f litex_param_fact_1 y litex_nested_param_fact_2
  exact litex_nested_param_fact_2

noncomputable def obj_28 (y : Litex.Object) : Litex.Object :=
  y

theorem obj_29_applicable : ∀ (f : Litex.Object) (litex_param_fact_1 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (y : Litex.Object) (litex_nested_param_fact_2 : Litex.In y Litex.R), Litex.Applicable f [(obj_28 y)] :=
by
  intro f litex_param_fact_1 y litex_nested_param_fact_2
  exact Litex.fnSetApplicable litex_param_fact_1 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In ((obj_28 y)) Litex.R, True
  exact Exists.intro ((well_defined_fact_8 f litex_param_fact_1 y litex_nested_param_fact_2)) (True.intro))

noncomputable def obj_29 (f : Litex.Object) (litex_param_fact_1 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (y : Litex.Object) (litex_nested_param_fact_2 : Litex.In y Litex.R) : Litex.Object :=
  f [(obj_28 y)] ((obj_29_applicable f litex_param_fact_1 y litex_nested_param_fact_2))

theorem obj_29_result : ∀ (f : Litex.Object) (litex_param_fact_1 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (y : Litex.Object) (litex_nested_param_fact_2 : Litex.In y Litex.R), Litex.In (obj_29 f litex_param_fact_1 y litex_nested_param_fact_2) Litex.R :=
by
  intro f litex_param_fact_1 y litex_nested_param_fact_2
  simpa [obj_29] using (Litex.fnSetResult litex_param_fact_1 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In ((obj_28 y)) Litex.R, True
  exact Exists.intro ((well_defined_fact_8 f litex_param_fact_1 y litex_nested_param_fact_2)) (True.intro)))

theorem well_defined_fact_9 : ∀ (f : Litex.Object) (litex_param_fact_1 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (y : Litex.Object) (litex_nested_param_fact_2 : Litex.In y Litex.R), Litex.In y Litex.C :=
by
  intro f litex_param_fact_1 y litex_nested_param_fact_2
  exact (Litex.BuiltinRules.realInComplex (litex_nested_param_fact_2))

theorem well_defined_fact_10 : ∀ (f : Litex.Object) (litex_param_fact_1 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (y : Litex.Object) (litex_nested_param_fact_2 : Litex.In y Litex.R), Litex.In 1 Litex.C :=
by
  intro f litex_param_fact_1 y litex_nested_param_fact_2
  exact Litex.BuiltinRules.numeralInC 1

theorem well_defined_fact_11 : ∀ (f : Litex.Object) (litex_param_fact_1 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (y : Litex.Object) (litex_nested_param_fact_2 : Litex.In y Litex.R), Litex.In 1 Litex.R :=
by
  intro f litex_param_fact_1 y litex_nested_param_fact_2
  exact Litex.BuiltinRules.numeralInR 1

theorem well_defined_fact_12 : ∀ (f : Litex.Object) (litex_param_fact_1 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (y : Litex.Object) (litex_nested_param_fact_2 : Litex.In y Litex.R), Litex.In (Litex.sub y 1 (well_defined_fact_9 f litex_param_fact_1 y litex_nested_param_fact_2) (well_defined_fact_10 f litex_param_fact_1 y litex_nested_param_fact_2)) Litex.R :=
by
  intro f litex_param_fact_1 y litex_nested_param_fact_2
  exact (Litex.BuiltinRules.realSubClosure ((well_defined_fact_9 f litex_param_fact_1 y litex_nested_param_fact_2)) ((well_defined_fact_10 f litex_param_fact_1 y litex_nested_param_fact_2)) (litex_nested_param_fact_2) (Litex.BuiltinRules.numeralInR 1))

noncomputable def obj_27 : Litex.Object :=
  Litex.R

noncomputable def obj_30 : Litex.Object :=
  1

noncomputable def obj_31 : Litex.Object :=
  Litex.C

noncomputable def obj_32 (f : Litex.Object) (litex_param_fact_1 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (y : Litex.Object) (litex_nested_param_fact_2 : Litex.In y Litex.R) : Litex.Object :=
  (Litex.sub (obj_28 y) obj_30 (well_defined_fact_9 f litex_param_fact_1 y litex_nested_param_fact_2) (well_defined_fact_10 f litex_param_fact_1 y litex_nested_param_fact_2))

theorem obj_33_applicable : ∀ (f : Litex.Object) (litex_param_fact_1 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (y : Litex.Object) (litex_nested_param_fact_2 : Litex.In y Litex.R), Litex.Applicable f [(obj_32 f litex_param_fact_1 y litex_nested_param_fact_2)] :=
by
  intro f litex_param_fact_1 y litex_nested_param_fact_2
  exact Litex.fnSetApplicable litex_param_fact_1 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In ((obj_32 f litex_param_fact_1 y litex_nested_param_fact_2)) Litex.R, True
  exact Exists.intro ((well_defined_fact_12 f litex_param_fact_1 y litex_nested_param_fact_2)) (True.intro))

noncomputable def obj_33 (f : Litex.Object) (litex_param_fact_1 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (y : Litex.Object) (litex_nested_param_fact_2 : Litex.In y Litex.R) : Litex.Object :=
  f [(obj_32 f litex_param_fact_1 y litex_nested_param_fact_2)] ((obj_33_applicable f litex_param_fact_1 y litex_nested_param_fact_2))

theorem obj_33_result : ∀ (f : Litex.Object) (litex_param_fact_1 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (y : Litex.Object) (litex_nested_param_fact_2 : Litex.In y Litex.R), Litex.In (obj_33 f litex_param_fact_1 y litex_nested_param_fact_2) Litex.R :=
by
  intro f litex_param_fact_1 y litex_nested_param_fact_2
  simpa [obj_33] using (Litex.fnSetResult litex_param_fact_1 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In ((obj_32 f litex_param_fact_1 y litex_nested_param_fact_2)) Litex.R, True
  exact Exists.intro ((well_defined_fact_12 f litex_param_fact_1 y litex_nested_param_fact_2)) (True.intro)))

theorem well_defined_fact_13 : ∀ (f : Litex.Object) (litex_param_fact_1 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (litex_domain_fact_1 : ∀ (y : Litex.Object) (litex_nested_param_fact_2 : Litex.In y Litex.R), (obj_29 f litex_param_fact_1 y litex_nested_param_fact_2) = (obj_33 f litex_param_fact_1 y litex_nested_param_fact_2)), Litex.In 2 Litex.R :=
by
  intro f litex_param_fact_1 litex_domain_fact_1
  exact Litex.BuiltinRules.numeralInR 2

noncomputable def obj_34 : Litex.Object :=
  2

noncomputable def obj_35 : Litex.Object :=
  Litex.R

theorem obj_36_applicable : ∀ (f : Litex.Object) (litex_param_fact_1 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (litex_domain_fact_1 : ∀ (y : Litex.Object) (litex_nested_param_fact_2 : Litex.In y Litex.R), (obj_29 f litex_param_fact_1 y litex_nested_param_fact_2) = (obj_33 f litex_param_fact_1 y litex_nested_param_fact_2)), Litex.Applicable f [obj_34] :=
by
  intro f litex_param_fact_1 litex_domain_fact_1
  exact Litex.fnSetApplicable litex_param_fact_1 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In (obj_34) Litex.R, True
  exact Exists.intro ((well_defined_fact_13 f litex_param_fact_1 litex_domain_fact_1)) (True.intro))

noncomputable def obj_36 (f : Litex.Object) (litex_param_fact_1 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (litex_domain_fact_1 : ∀ (y : Litex.Object) (litex_nested_param_fact_2 : Litex.In y Litex.R), (obj_29 f litex_param_fact_1 y litex_nested_param_fact_2) = (obj_33 f litex_param_fact_1 y litex_nested_param_fact_2)) : Litex.Object :=
  f [obj_34] ((obj_36_applicable f litex_param_fact_1 litex_domain_fact_1))

theorem obj_36_result : ∀ (f : Litex.Object) (litex_param_fact_1 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (litex_domain_fact_1 : ∀ (y : Litex.Object) (litex_nested_param_fact_2 : Litex.In y Litex.R), (obj_29 f litex_param_fact_1 y litex_nested_param_fact_2) = (obj_33 f litex_param_fact_1 y litex_nested_param_fact_2)), Litex.In (obj_36 f litex_param_fact_1 litex_domain_fact_1) Litex.R :=
by
  intro f litex_param_fact_1 litex_domain_fact_1
  simpa [obj_36] using (Litex.fnSetResult litex_param_fact_1 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In (obj_34) Litex.R, True
  exact Exists.intro ((well_defined_fact_13 f litex_param_fact_1 litex_domain_fact_1)) (True.intro)))

theorem well_defined_fact_14 : ∀ (f : Litex.Object) (litex_param_fact_1 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (litex_domain_fact_1 : ∀ (y : Litex.Object) (litex_nested_param_fact_2 : Litex.In y Litex.R), (obj_29 f litex_param_fact_1 y litex_nested_param_fact_2) = (obj_33 f litex_param_fact_1 y litex_nested_param_fact_2)), Litex.In 1 Litex.R :=
by
  intro f litex_param_fact_1 litex_domain_fact_1
  exact Litex.BuiltinRules.numeralInR 1

noncomputable def obj_37 : Litex.Object :=
  1

theorem obj_38_applicable : ∀ (f : Litex.Object) (litex_param_fact_1 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (litex_domain_fact_1 : ∀ (y : Litex.Object) (litex_nested_param_fact_2 : Litex.In y Litex.R), (obj_29 f litex_param_fact_1 y litex_nested_param_fact_2) = (obj_33 f litex_param_fact_1 y litex_nested_param_fact_2)), Litex.Applicable f [obj_37] :=
by
  intro f litex_param_fact_1 litex_domain_fact_1
  exact Litex.fnSetApplicable litex_param_fact_1 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In (obj_37) Litex.R, True
  exact Exists.intro ((well_defined_fact_14 f litex_param_fact_1 litex_domain_fact_1)) (True.intro))

noncomputable def obj_38 (f : Litex.Object) (litex_param_fact_1 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (litex_domain_fact_1 : ∀ (y : Litex.Object) (litex_nested_param_fact_2 : Litex.In y Litex.R), (obj_29 f litex_param_fact_1 y litex_nested_param_fact_2) = (obj_33 f litex_param_fact_1 y litex_nested_param_fact_2)) : Litex.Object :=
  f [obj_37] ((obj_38_applicable f litex_param_fact_1 litex_domain_fact_1))

theorem obj_38_result : ∀ (f : Litex.Object) (litex_param_fact_1 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (litex_domain_fact_1 : ∀ (y : Litex.Object) (litex_nested_param_fact_2 : Litex.In y Litex.R), (obj_29 f litex_param_fact_1 y litex_nested_param_fact_2) = (obj_33 f litex_param_fact_1 y litex_nested_param_fact_2)), Litex.In (obj_38 f litex_param_fact_1 litex_domain_fact_1) Litex.R :=
by
  intro f litex_param_fact_1 litex_domain_fact_1
  simpa [obj_38] using (Litex.fnSetResult litex_param_fact_1 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In (obj_37) Litex.R, True
  exact Exists.intro ((well_defined_fact_14 f litex_param_fact_1 litex_domain_fact_1)) (True.intro)))

theorem fact22 : ∀ (f : Litex.Object) (litex_param_fact_1 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (litex_domain_fact_1 : ∀ (y : Litex.Object) (litex_nested_param_fact_2 : Litex.In y Litex.R), (obj_29 f litex_param_fact_1 y litex_nested_param_fact_2) = (obj_33 f litex_param_fact_1 y litex_nested_param_fact_2)), (obj_36 f litex_param_fact_1 litex_domain_fact_1) = (obj_38 f litex_param_fact_1 litex_domain_fact_1) :=
by
  intro f litex_param_fact_1 litex_domain_fact_1
  exact (by
  have litex_normalization_source := ((litex_domain_fact_1 (Litex.add 1 1 (Litex.BuiltinRules.numeralInC 1) (Litex.BuiltinRules.numeralInC 1)) ((Litex.BuiltinRules.realAddClosure ((Litex.BuiltinRules.numeralInC 1)) ((Litex.BuiltinRules.numeralInC 1)) (Litex.BuiltinRules.numeralInR 1) (Litex.BuiltinRules.numeralInR 1)))))
  simp only [OfNat.ofNat, Litex.add_embedComplex, Litex.sub_embedComplex, Litex.mul_embedComplex, Litex.div_embedComplex, obj_27, obj_28, obj_29, obj_30, obj_31, obj_32, obj_33, obj_34, obj_35, obj_36, obj_37, obj_38] at litex_normalization_source ⊢
  norm_num at litex_normalization_source ⊢
  exact litex_normalization_source)
```
<!-- END ACTUAL GENERATED LEAN: arithmetic_forall_wd -->

Required generated shape:

```lean
theorem well_defined_fact_<sub> : Litex.In (Litex.sub y 1) Litex.R := by
  exact Litex.BuiltinRules.realSubClosure y 1 y_in_R one_in_R

theorem fact_<forall> : ∀ (f : Litex.Object), ... := by ...
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
import Litex.BuiltinRules

example : Litex.abiVersion = 8 := rfl

axiom marked : Litex.Object → Prop

def is_zero (x : Litex.Object) : Prop :=
  Litex.In x Litex.R ∧ (x = 0)

theorem fact3 : is_zero 0 := by
  exact (by
  change Litex.In 0 Litex.R ∧ ((0 : Litex.Object) = 0)
  exact And.intro (Litex.BuiltinRules.numeralInR 0) ((rfl)))

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
import Litex.BuiltinRules

example : Litex.abiVersion = 8 := rfl

theorem fact13 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.IsSet a) (b : Litex.Object) (litex_param_fact_2 : Litex.IsSet b) (litex_domain_fact_1 : a = b), b = a :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact (Eq.symm (litex_domain_fact_1))

theorem fact32 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.IsSet a) (b : Litex.Object) (litex_param_fact_2 : Litex.IsSet b) (c : Litex.Object) (litex_param_fact_3 : Litex.IsSet c) (litex_domain_fact_1 : a = b) (litex_domain_fact_2 : b = c), a = c :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3 litex_domain_fact_1 litex_domain_fact_2
  exact (Eq.trans ((litex_domain_fact_1)) ((litex_domain_fact_2)))
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
import Litex.BuiltinRules

example : Litex.abiVersion = 8 := rfl

theorem fact27 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (litex_domain_fact_1 : a = 1), Litex.In 1 Litex.R :=
by
  intro a litex_param_fact_1 litex_domain_fact_1
  exact Litex.BuiltinRules.numeralInR 1

theorem fact28 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (litex_domain_fact_1 : a = 1), Litex.In a Litex.R :=
by
  intro a litex_param_fact_1 litex_domain_fact_1
  exact by simpa only [litex_domain_fact_1] using (fact27 a litex_param_fact_1 litex_domain_fact_1)

theorem well_defined_fact_2 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (f : Litex.Object) (litex_param_fact_2 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (litex_domain_fact_1 : a = 1), Litex.In a Litex.R :=
by
  intro a litex_param_fact_1 f litex_param_fact_2 litex_domain_fact_1
  exact by simpa only [litex_domain_fact_1] using (fact27 a litex_param_fact_1 litex_domain_fact_1)

theorem well_defined_fact_3 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (f : Litex.Object) (litex_param_fact_2 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (litex_domain_fact_1 : a = 1), Litex.In a Litex.R :=
by
  intro a litex_param_fact_1 f litex_param_fact_2 litex_domain_fact_1
  exact fact28 a litex_param_fact_1 litex_domain_fact_1

noncomputable def obj_14 (a : Litex.Object) : Litex.Object :=
  a

theorem obj_24_applicable : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (f : Litex.Object) (litex_param_fact_2 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (litex_domain_fact_1 : a = 1), Litex.Applicable f [(obj_14 a)] :=
by
  intro a litex_param_fact_1 f litex_param_fact_2 litex_domain_fact_1
  exact Litex.fnSetApplicable litex_param_fact_2 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In ((obj_14 a)) Litex.R, True
  exact Exists.intro ((well_defined_fact_3 a litex_param_fact_1 f litex_param_fact_2 litex_domain_fact_1)) (True.intro))

noncomputable def obj_24 (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (f : Litex.Object) (litex_param_fact_2 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (litex_domain_fact_1 : a = 1) : Litex.Object :=
  f [(obj_14 a)] ((obj_24_applicable a litex_param_fact_1 f litex_param_fact_2 litex_domain_fact_1))

theorem obj_24_result : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (f : Litex.Object) (litex_param_fact_2 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (litex_domain_fact_1 : a = 1), Litex.In (obj_24 a litex_param_fact_1 f litex_param_fact_2 litex_domain_fact_1) Litex.R :=
by
  intro a litex_param_fact_1 f litex_param_fact_2 litex_domain_fact_1
  simpa [obj_24] using (Litex.fnSetResult litex_param_fact_2 rfl (by
  change ∃ litex_application_requirement_1 : Litex.In ((obj_14 a)) Litex.R, True
  exact Exists.intro ((well_defined_fact_3 a litex_param_fact_1 f litex_param_fact_2 litex_domain_fact_1)) (True.intro)))

theorem fact26 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (f : Litex.Object) (litex_param_fact_2 : Litex.In f (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => ∃ litex_requirement_1 : Litex.In (Litex.arg litex_args_0 0) Litex.R, True, range := fun litex_args_0 _ _ => Litex.R } : Litex.FnSpec))) (litex_domain_fact_1 : a = 1), (obj_24 a litex_param_fact_1 f litex_param_fact_2 litex_domain_fact_1) = (obj_24 a litex_param_fact_1 f litex_param_fact_2 litex_domain_fact_1) :=
by
  intro a litex_param_fact_1 f litex_param_fact_2 litex_domain_fact_1
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
import Litex.BuiltinRules

example : Litex.abiVersion = 8 := rfl

theorem fact13 : ∀ (s : Litex.Object) (litex_param_fact_1 : Litex.IsNonemptySet s), s = s :=
by
  intro s litex_param_fact_1
  exact rfl

theorem fact14 : ∀ (t : Litex.Object) (litex_param_fact_1 : Litex.IsFiniteSet t), t = t :=
by
  intro t litex_param_fact_1
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
import Litex.BuiltinRules

example : Litex.abiVersion = 8 := rfl

theorem fact13 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.IsSet a) (b : Litex.Object) (litex_param_fact_2 : Litex.IsSet b) (litex_domain_fact_1 : a ≠ b), b ≠ a :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact (Litex.BuiltinRules.notEqualSymmetry (litex_domain_fact_1))

theorem fact14 : Litex.In 1 Litex.N := by
  exact Litex.BuiltinRules.numeralInN 1

theorem fact15 : Litex.Le 0 1 := by
  exact (by
  exact (Litex.BuiltinRules.numeralLe 0 1).2 (by norm_num))

theorem fact17 : Litex.In 1 Litex.C := by
  exact Litex.BuiltinRules.numeralInC 1
```
<!-- END ACTUAL GENERATED LEAN: shared_builtin_rules -->

Required generated shape:

```lean
import Litex.BuiltinRules

exact Litex.BuiltinRules.notEqualSymmetry fact_<a_ne_b>
exact Litex.BuiltinRules.numeralInN 1
exact Litex.BuiltinRules.numeralInC 1
```

Boundary: a verifier builtin without a checked shared-theorem adapter remains
unsupported; the compiler does not generate an inline proof or axiom fallback.
