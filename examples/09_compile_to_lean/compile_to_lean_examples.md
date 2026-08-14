# Litex-to-Lean executable feature ledger

This file grows with the compiler. Each newly supported To-Lean capability
appends one section containing the exact self-contained Litex program exercised
by its harness, the complete Lean file actually emitted by the current
compiler, the essential required shape, the nearest rejected boundary, and the
focused gates that establish the claim. A required shape is an assertion about
the output; it is never a substitute for showing the output itself.

The Rust ledger harness compiles every `litex` fence independently and compares
the result byte-for-byte with the adjacent `Actual generated Lean` snapshot.
The real Lean gate then compiles every complete generated file against the
shared `Litex.Core` and `Litex.BuiltinRules` Mathlib project. If a proposed
program does not currently emit Lean, its section must say `TODO` with the
current compiler error instead of presenting a required shape as implemented.
New entries are appended in implementation order; once an entry is
established, later work extends the ledger instead of replacing its history.

Generated output uses ABI version 7 and one `Litex.Object` universe. No entry
may reintroduce native numeric binders, `Set ℝ`, carrier unification, widening,
downcasts, target-side proof search, `sorry`, or a compiler-invented axiom.

## well_defined_object_dag

Harness source:
[`compile_to_lean_well_defined_object_dag.lit`](../05_compiler_interop/compile_to_lean_well_defined_object_dag.lit).

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

example : Litex.abiVersion = 7 := rfl

theorem well_defined_fact_7 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R ∧ (Litex.In (Litex.arg litex_args_0 1) Litex.R), range := fun litex_args_0 => Litex.R } : Litex.FnSpec))), Litex.In a Litex.R :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5
  exact litex_param_fact_1

noncomputable def obj_25 (a : Litex.Object) : Litex.Object :=
  a

theorem obj_44_applicable : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R ∧ (Litex.In (Litex.arg litex_args_0 1) Litex.R), range := fun litex_args_0 => Litex.R } : Litex.FnSpec))), Litex.Applicable g [(obj_25 a)] :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5
  exact Litex.fnSetApplicable litex_param_fact_3 rfl (by simpa [Litex.arg] using ((well_defined_fact_7 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5)))

noncomputable def obj_44 (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R ∧ (Litex.In (Litex.arg litex_args_0 1) Litex.R), range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) : Litex.Object :=
  g [(obj_25 a)] ((obj_44_applicable a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5))

theorem obj_44_result : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R ∧ (Litex.In (Litex.arg litex_args_0 1) Litex.R), range := fun litex_args_0 => Litex.R } : Litex.FnSpec))), Litex.In (obj_44 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5) Litex.R :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5
  simpa [obj_44] using (Litex.fnSetResult litex_param_fact_3 rfl (by simpa [Litex.arg] using ((well_defined_fact_7 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5))))

theorem well_defined_fact_8 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R ∧ (Litex.In (Litex.arg litex_args_0 1) Litex.R), range := fun litex_args_0 => Litex.R } : Litex.FnSpec))), Litex.In b Litex.R :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5
  exact litex_param_fact_2

noncomputable def obj_26 (b : Litex.Object) : Litex.Object :=
  b

theorem obj_45_applicable : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R ∧ (Litex.In (Litex.arg litex_args_0 1) Litex.R), range := fun litex_args_0 => Litex.R } : Litex.FnSpec))), Litex.Applicable t [(obj_26 b)] :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5
  exact Litex.fnSetApplicable litex_param_fact_4 rfl (by simpa [Litex.arg] using ((well_defined_fact_8 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5)))

noncomputable def obj_45 (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R ∧ (Litex.In (Litex.arg litex_args_0 1) Litex.R), range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) : Litex.Object :=
  t [(obj_26 b)] ((obj_45_applicable a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5))

theorem obj_45_result : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R ∧ (Litex.In (Litex.arg litex_args_0 1) Litex.R), range := fun litex_args_0 => Litex.R } : Litex.FnSpec))), Litex.In (obj_45 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5) Litex.R :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5
  simpa [obj_45] using (Litex.fnSetResult litex_param_fact_4 rfl (by simpa [Litex.arg] using ((well_defined_fact_8 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5))))

theorem well_defined_fact_9 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R ∧ (Litex.In (Litex.arg litex_args_0 1) Litex.R), range := fun litex_args_0 => Litex.R } : Litex.FnSpec))), Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec)) :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5
  exact litex_param_fact_3

theorem well_defined_fact_10 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R ∧ (Litex.In (Litex.arg litex_args_0 1) Litex.R), range := fun litex_args_0 => Litex.R } : Litex.FnSpec))), Litex.In (g [a] (Litex.fnSetApplicable litex_param_fact_3 rfl (by simpa [Litex.arg] using ((well_defined_fact_7 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5))))) Litex.R :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5
  exact (by simpa using (Litex.fnSetResult litex_param_fact_3 rfl (by simpa [Litex.arg] using ((well_defined_fact_7 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5)))))

theorem well_defined_fact_11 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R ∧ (Litex.In (Litex.arg litex_args_0 1) Litex.R), range := fun litex_args_0 => Litex.R } : Litex.FnSpec))), Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec)) :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5
  exact litex_param_fact_4

theorem well_defined_fact_12 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R ∧ (Litex.In (Litex.arg litex_args_0 1) Litex.R), range := fun litex_args_0 => Litex.R } : Litex.FnSpec))), Litex.In (t [b] (Litex.fnSetApplicable litex_param_fact_4 rfl (by simpa [Litex.arg] using ((well_defined_fact_8 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5))))) Litex.R :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5
  exact (by simpa using (Litex.fnSetResult litex_param_fact_4 rfl (by simpa [Litex.arg] using ((well_defined_fact_8 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5)))))

noncomputable def obj_24 : Litex.Object :=
  Litex.R

theorem obj_46_applicable : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R ∧ (Litex.In (Litex.arg litex_args_0 1) Litex.R), range := fun litex_args_0 => Litex.R } : Litex.FnSpec))), Litex.Applicable f [(obj_44 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5), (obj_45 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5)] :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5
  exact Litex.fnSetApplicable litex_param_fact_5 rfl (by simpa [Litex.arg] using (And.intro ((well_defined_fact_10 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5)) ((well_defined_fact_12 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5))))

noncomputable def obj_46 (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R ∧ (Litex.In (Litex.arg litex_args_0 1) Litex.R), range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) : Litex.Object :=
  f [(obj_44 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5), (obj_45 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5)] ((obj_46_applicable a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5))

theorem obj_46_result : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R ∧ (Litex.In (Litex.arg litex_args_0 1) Litex.R), range := fun litex_args_0 => Litex.R } : Litex.FnSpec))), Litex.In (obj_46 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5) Litex.R :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5
  simpa [obj_46] using (Litex.fnSetResult litex_param_fact_5 rfl (by simpa [Litex.arg] using (And.intro ((well_defined_fact_10 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5)) ((well_defined_fact_12 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5)))))

theorem fact43 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.R) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.R) (g : Litex.Object) (litex_param_fact_3 : Litex.In g (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (t : Litex.Object) (litex_param_fact_4 : Litex.In t (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec))) (f : Litex.Object) (litex_param_fact_5 : Litex.In f (Litex.FnSet ({ arity := 2, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R ∧ (Litex.In (Litex.arg litex_args_0 1) Litex.R), range := fun litex_args_0 => Litex.R } : Litex.FnSpec))), (obj_46 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5) = (obj_46 a litex_param_fact_1 b litex_param_fact_2 g litex_param_fact_3 t litex_param_fact_4 f litex_param_fact_5) :=
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

Focused gates:

```text
target/release/litex -compact -isolated -runner -f examples/05_compiler_interop/compile_to_lean_well_defined_object_dag.lit
cargo test --release nested_function_application_dag_names_each_direct_child_before_parent -- --nocapture
cargo test --release scoped_nested_applications_emit_stable_object_aliases -- --nocapture
LITEX_LEAN_PROJECT=lean cargo test --release scoped_nested_object_aliases_compile_with_mathlib -- --ignored --nocapture
```

## trusted_forall_atomic_fact

Harness source:
[`compile_to_lean_trusted_forall_instantiation.lit`](../05_compiler_interop/compile_to_lean_trusted_forall_instantiation.lit).

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

example : Litex.abiVersion = 7 := rfl

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

Focused gates:

```text
target/release/litex -compact -isolated -runner -f examples/05_compiler_interop/compile_to_lean_trusted_forall_instantiation.lit
cargo test --release trusted_forall_atomic_fact_replays_exact_fact_id -- --nocapture
cargo test --release atomic_abstract_prop_without_known_forall_remains_rejected -- --nocapture
LITEX_LEAN_PROJECT=lean cargo test --release trusted_forall_atomic_fact_compiles_with_mathlib -- --ignored --nocapture
```

## proof_carrying_arithmetic

Harness source:
[`compile_to_lean_proof_carrying_arithmetic.lit`](../05_compiler_interop/compile_to_lean_proof_carrying_arithmetic.lit).

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
        (a / b) + a = (a / b) + a
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: proof_carrying_arithmetic -->
```lean
import Litex.BuiltinRules

example : Litex.abiVersion = 7 := rfl

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

theorem well_defined_fact_36 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (litex_domain_fact_1 : b ≠ 0), b ≠ 0 :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact litex_domain_fact_1

theorem well_defined_fact_37 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (litex_domain_fact_1 : b ≠ 0), Litex.In a Litex.C :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact litex_param_fact_1

theorem well_defined_fact_38 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (litex_domain_fact_1 : b ≠ 0), Litex.In b Litex.C :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact litex_param_fact_2

theorem well_defined_fact_39 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (litex_domain_fact_1 : b ≠ 0), Litex.In (Litex.div a b (well_defined_fact_37 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) (well_defined_fact_38 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) (well_defined_fact_36 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1)) Litex.C :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact (Litex.BuiltinRules.complexDivClosure ((well_defined_fact_37 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1)) ((well_defined_fact_38 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1)) ((well_defined_fact_36 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1)))

theorem well_defined_fact_40 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (litex_domain_fact_1 : b ≠ 0), Litex.In a Litex.C :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact litex_param_fact_1

noncomputable def obj_46 : Litex.Object :=
  Litex.C

noncomputable def obj_47 (a : Litex.Object) : Litex.Object :=
  a

noncomputable def obj_48 (b : Litex.Object) : Litex.Object :=
  b

noncomputable def obj_50 (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (litex_domain_fact_1 : b ≠ 0) : Litex.Object :=
  (Litex.div (obj_47 a) (obj_48 b) (well_defined_fact_37 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) (well_defined_fact_38 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) (well_defined_fact_36 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1))

noncomputable def obj_51 (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (litex_domain_fact_1 : b ≠ 0) : Litex.Object :=
  (Litex.add (obj_50 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) (obj_47 a) (well_defined_fact_39 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) (well_defined_fact_40 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1))

theorem fact39 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.In a Litex.C) (b : Litex.Object) (litex_param_fact_2 : Litex.In b Litex.C) (litex_domain_fact_1 : b ≠ 0), (obj_51 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) = (obj_51 a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1) :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 litex_domain_fact_1
  exact rfl
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

Focused gates:

```text
target/release/litex -compact -isolated -runner -f examples/05_compiler_interop/compile_to_lean_proof_carrying_arithmetic.lit
cargo test --release proof_carrying_arithmetic_replays_well_defined_fact_ids -- --nocapture
cargo test --release missing_divisor_nonzero_well_definedness_role_is_rejected -- --nocapture
LITEX_LEAN_PROJECT=lean cargo test --release proof_carrying_arithmetic_compiles_with_mathlib -- --ignored --nocapture
```

## inferred_forall_premise

Harness source:
[`compile_to_lean_inferred_forall_premise.lit`](../05_compiler_interop/compile_to_lean_inferred_forall_premise.lit).

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

example : Litex.abiVersion = 7 := rfl

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

Focused gates:

```text
target/release/litex -compact -isolated -runner -f examples/05_compiler_interop/compile_to_lean_inferred_forall_premise.lit
cargo test --release inferred_forall_premise_replays_its_exact_fact_id -- --nocapture
cargo test --release unsupported_inferred_forall_premise_remains_rejected -- --nocapture
LITEX_LEAN_PROJECT=lean cargo test --release inferred_forall_premise_compiles_with_mathlib -- --ignored --nocapture
```

## proof_carrying_list_set

Harness source:
[`compile_to_lean_proof_carrying_list_set.lit`](../05_compiler_interop/compile_to_lean_proof_carrying_list_set.lit).

A finite set literal consumes the exact WD construction recipe checked by
Litex: one ordered child object per source entry and one indexed inequality for
every pair `i < j`. The emitter names every child and every retained fact, then
builds `ListSetWellDefined` without searching for distinctness in Lean.

```litex
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

example : Litex.abiVersion = 7 := rfl

theorem well_defined_fact_4 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.IsSet a) (b : Litex.Object) (litex_param_fact_2 : Litex.IsSet b) (c : Litex.Object) (litex_param_fact_3 : Litex.IsSet c) (litex_domain_fact_1 : a ≠ b) (litex_domain_fact_2 : a ≠ c) (litex_domain_fact_3 : b ≠ c), a ≠ b :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3 litex_domain_fact_1 litex_domain_fact_2 litex_domain_fact_3
  exact litex_domain_fact_1

theorem well_defined_fact_5 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.IsSet a) (b : Litex.Object) (litex_param_fact_2 : Litex.IsSet b) (c : Litex.Object) (litex_param_fact_3 : Litex.IsSet c) (litex_domain_fact_1 : a ≠ b) (litex_domain_fact_2 : a ≠ c) (litex_domain_fact_3 : b ≠ c), a ≠ c :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3 litex_domain_fact_1 litex_domain_fact_2 litex_domain_fact_3
  exact litex_domain_fact_2

theorem well_defined_fact_6 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.IsSet a) (b : Litex.Object) (litex_param_fact_2 : Litex.IsSet b) (c : Litex.Object) (litex_param_fact_3 : Litex.IsSet c) (litex_domain_fact_1 : a ≠ b) (litex_domain_fact_2 : a ≠ c) (litex_domain_fact_3 : b ≠ c), b ≠ c :=
by
  intro a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3 litex_domain_fact_1 litex_domain_fact_2 litex_domain_fact_3
  exact litex_domain_fact_3

noncomputable def obj_5 (a : Litex.Object) : Litex.Object :=
  a

noncomputable def obj_6 (b : Litex.Object) : Litex.Object :=
  b

noncomputable def obj_7 (c : Litex.Object) : Litex.Object :=
  c

noncomputable def obj_8 (a : Litex.Object) (litex_param_fact_1 : Litex.IsSet a) (b : Litex.Object) (litex_param_fact_2 : Litex.IsSet b) (c : Litex.Object) (litex_param_fact_3 : Litex.IsSet c) (litex_domain_fact_1 : a ≠ b) (litex_domain_fact_2 : a ≠ c) (litex_domain_fact_3 : b ≠ c) : Litex.Object :=
  (Litex.listSet [(obj_5 a), (obj_6 b), (obj_7 c)] (by
  apply List.Pairwise.cons
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (hx_0 | hx_1)
    · subst x
      exact (well_defined_fact_4 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3 litex_domain_fact_1 litex_domain_fact_2 litex_domain_fact_3)
    · subst x
      exact (well_defined_fact_5 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3 litex_domain_fact_1 litex_domain_fact_2 litex_domain_fact_3)
  · apply List.Pairwise.cons
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      subst x
      exact (well_defined_fact_6 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3 litex_domain_fact_1 litex_domain_fact_2 litex_domain_fact_3)
    · apply List.Pairwise.cons
      · intro x hx
        simp only [List.not_mem_nil] at hx
      · exact List.Pairwise.nil))

theorem fact22 : ∀ (a : Litex.Object) (litex_param_fact_1 : Litex.IsSet a) (b : Litex.Object) (litex_param_fact_2 : Litex.IsSet b) (c : Litex.Object) (litex_param_fact_3 : Litex.IsSet c) (litex_domain_fact_1 : a ≠ b) (litex_domain_fact_2 : a ≠ c) (litex_domain_fact_3 : b ≠ c), (obj_8 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3 litex_domain_fact_1 litex_domain_fact_2 litex_domain_fact_3) = (obj_8 a litex_param_fact_1 b litex_param_fact_2 c litex_param_fact_3 litex_domain_fact_1 litex_domain_fact_2 litex_domain_fact_3) :=
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

Focused gates:

```text
target/release/litex -compact -isolated -runner -f examples/05_compiler_interop/compile_to_lean_proof_carrying_list_set.lit
cargo test --release compile_to_lean_capture_retains_list_set_children_and_pairwise_requirements -- --nocapture
cargo test --release proof_carrying_list_set_replays_indexed_well_definedness -- --nocapture
cargo test --release missing_list_set_pairwise_well_definedness_role_is_rejected -- --nocapture
LITEX_LEAN_PROJECT=lean cargo test --release proof_carrying_list_set_compiles_with_mathlib -- --ignored --nocapture
```

## object_choice

[`compile_to_lean_object_choice.lit`](../05_compiler_interop/compile_to_lean_object_choice.lit)
adds one noncomputable object from the verifier-owned nonempty-set proof.

```litex
have x R
x $in R
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: object_choice -->
```lean
import Litex.BuiltinRules

example : Litex.abiVersion = 7 := rfl

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

Focused gates: `object_choice_emits_one_definition_and_exact_membership_fact`
and `object_choice_compiles_with_mathlib`.

## existential_intro_elim

[`compile_to_lean_existential_intro_elim.lit`](../05_compiler_interop/compile_to_lean_existential_intro_elim.lit)
replays introduction and ordered type/body projections.

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

example : Litex.abiVersion = 7 := rfl

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

Focused gates: `existential_intro_and_elim_replay_exact_projection_roles` and
`existential_intro_and_elim_compile_with_mathlib`.

## case_and_contradiction_scopes

[`compile_to_lean_case_and_contradiction_scopes.lit`](../05_compiler_interop/compile_to_lean_case_and_contradiction_scopes.lit)
keeps case and reverse-assumption `FactId`s local.

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

example : Litex.abiVersion = 7 := rfl

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

Focused gates: `case_and_contradiction_scopes_replay_local_fact_ids` and
`case_and_contradiction_scopes_compile_with_mathlib`.

## named_theorem

[`compile_to_lean_named_theorem.lit`](../05_compiler_interop/compile_to_lean_named_theorem.lit)
makes the source name own the complete forall.

```litex
thm one_eq_one:
    ? forall:
        1 = 1
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: named_theorem -->
```lean
import Litex.BuiltinRules

example : Litex.abiVersion = 7 := rfl

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

Focused gates: `named_theorem_emits_its_source_name_and_fact_id_binding` and
`named_theorem_compiles_with_mathlib`.

## total_object_constructors

[`compile_to_lean_total_object_constructors.lit`](../05_compiler_interop/compile_to_lean_total_object_constructors.lit)
adds a closed constant and total binary set constructor.

```litex
pi = pi
forall A, B set:
    union(A, B) = union(A, B)
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: total_object_constructors -->
```lean
import Litex.BuiltinRules

example : Litex.abiVersion = 7 := rfl

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

Focused gates: `total_object_constructors_render_without_proof_arguments` and
`total_object_constructors_compile_with_mathlib`.

## proof_carrying_division

[`compile_to_lean_proof_carrying_division.lit`](../05_compiler_interop/compile_to_lean_proof_carrying_division.lit)
isolates the partial division contract.

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

example : Litex.abiVersion = 7 := rfl

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

Focused gates: `proof_carrying_arithmetic_replays_well_defined_fact_ids`,
`missing_divisor_nonzero_well_definedness_role_is_rejected`, and
`proof_carrying_arithmetic_compiles_with_mathlib`.

## set_builder_scope

[`compile_to_lean_set_builder_scope.lit`](../05_compiler_interop/compile_to_lean_set_builder_scope.lit)
owns its predicate binder by `SymbolId`.

```litex
have S set = {x R: x = x}
S = S
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: set_builder_scope -->
```lean
import Litex.BuiltinRules

example : Litex.abiVersion = 7 := rfl

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

Focused gates: `set_builder_scope_uses_a_nonleaking_symbol_id_binder` and
`set_builder_scope_compiles_with_mathlib`.

## named_function

[`compile_to_lean_named_function.lit`](../05_compiler_interop/compile_to_lean_named_function.lit)
emits a checked body, range proof, membership, definition, and replay.

```litex
have fn id(x R) R = x
id(1) = 1
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: named_function -->
```lean
import Litex.BuiltinRules

example : Litex.abiVersion = 7 := rfl

noncomputable def litex_id_spec : Litex.FnSpec :=
  ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec)

noncomputable def litex_id_body (litex_function_args : List Litex.Object) : Litex.Object :=
  Litex.arg litex_function_args 0

theorem litex_id_closed :
    ∀ litex_function_args, litex_function_args.length = litex_id_spec.arity →
      litex_id_spec.requirements litex_function_args →
      Litex.In (litex_id_body litex_function_args) (litex_id_spec.range litex_function_args) :=
by
  intro litex_function_args litex_function_length litex_function_requirements
  change Litex.In (Litex.arg litex_function_args 0) Litex.R at litex_function_requirements
  change Litex.In (Litex.arg litex_function_args 0) Litex.R
  exact litex_function_requirements

noncomputable def litex_id_implementation : Litex.Object :=
  Litex.functionObject litex_id_spec litex_id_body litex_id_closed

noncomputable def litex_id : Litex.Object := litex_id_implementation

theorem fact5 : Litex.In litex_id (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec)) := by
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
  exact Litex.fnSetApplicable fact5 rfl (by simpa [Litex.arg] using (well_defined_fact_2))

noncomputable def obj_15 : Litex.Object :=
  litex_id [obj_13] (obj_15_applicable)

theorem obj_15_result : Litex.In obj_15 Litex.R :=
by
  simpa [obj_15] using (Litex.fnSetResult fact5 rfl (by simpa [Litex.arg] using (well_defined_fact_2)))

theorem fact7 : obj_15 = 1 := by
  exact (by
  change (litex_id [1] (obj_15_applicable)) = 1
  simp only [fact6, litex_id_implementation, litex_id_body, Litex.functionObject_apply, Litex.arg, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil])
```
<!-- END ACTUAL GENERATED LEAN: named_function -->

Lean uses `Litex.functionObject`, `functionObjectInFnSet`, and
`functionObject_apply`. An unavailable defining-equality `FactId` fails.

```lean
def id_spec : Litex.FnSpec := ...
def id_body (args : List Litex.Object) : Litex.Object := Litex.arg args 0
theorem id_closed : ... := by ...
noncomputable def id := Litex.functionObject id_spec id_body id_closed
```

Focused gates: `named_function_emits_checked_constructor_and_definition_replay`
and `named_function_compiles_with_mathlib`.

## indexed_aggregate

[`compile_to_lean_indexed_aggregate.lit`](../05_compiler_interop/compile_to_lean_indexed_aggregate.lit)
adds one tuple recipe before generalizing aggregate families.

```litex
have tuple q for i1 <= 2, q[i1] = 0
q = q
```

Actual generated Lean (current compiler snapshot):

<!-- BEGIN ACTUAL GENERATED LEAN: indexed_aggregate -->
```lean
import Litex.BuiltinRules

example : Litex.abiVersion = 7 := rfl

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

Focused gates: `indexed_aggregate_emits_one_checked_tuple_recipe` and
`indexed_aggregate_compiles_with_mathlib`.

## statement_object_interactions

[`compile_to_lean_statement_object_interactions.lit`](../05_compiler_interop/compile_to_lean_statement_object_interactions.lit)
contains the three deliberate cross-family probes.

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

example : Litex.abiVersion = 7 := rfl

noncomputable def litex_id_spec : Litex.FnSpec :=
  ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec)

noncomputable def litex_id_body (litex_function_args : List Litex.Object) : Litex.Object :=
  Litex.arg litex_function_args 0

theorem litex_id_closed :
    ∀ litex_function_args, litex_function_args.length = litex_id_spec.arity →
      litex_id_spec.requirements litex_function_args →
      Litex.In (litex_id_body litex_function_args) (litex_id_spec.range litex_function_args) :=
by
  intro litex_function_args litex_function_length litex_function_requirements
  change Litex.In (Litex.arg litex_function_args 0) Litex.R at litex_function_requirements
  change Litex.In (Litex.arg litex_function_args 0) Litex.R
  exact litex_function_requirements

noncomputable def litex_id_implementation : Litex.Object :=
  Litex.functionObject litex_id_spec litex_id_body litex_id_closed

noncomputable def litex_id : Litex.Object := litex_id_implementation

theorem fact5 : Litex.In litex_id (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => Litex.R } : Litex.FnSpec)) := by
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
  exact Litex.fnSetApplicable fact5 rfl (by simpa [Litex.arg] using (well_defined_fact_2))

noncomputable def obj_33 : Litex.Object :=
  litex_id [obj_30] (obj_33_applicable)

theorem obj_33_result : Litex.In obj_33 Litex.R :=
by
  simpa [obj_33] using (Litex.fnSetResult fact5 rfl (by simpa [Litex.arg] using (well_defined_fact_2)))

theorem fact21 : obj_33 = y := by
  exact (by
  change (litex_id [y] (obj_33_applicable)) = y
  simp only [fact6, litex_id_implementation, litex_id_body, Litex.functionObject_apply, Litex.arg, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil])

theorem one_eq_one_by_cases : (1 : Litex.Object) = 1 :=
by
  have litex_theorem_step_1 : (1 : Litex.Object) = 1 := by
    exact (by
  have litex_case_1 : (1 : Litex.Object) = 1 := rfl
  exact litex_case_1)
  exact rfl

noncomputable def into_builder_spec : Litex.FnSpec :=
  ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => (Litex.setBuilder Litex.R (fun litex_set_builder_9 => litex_set_builder_9 = litex_set_builder_9)) } : Litex.FnSpec)

noncomputable def into_builder_body (litex_function_args : List Litex.Object) : Litex.Object :=
  Litex.arg litex_function_args 0

theorem into_builder_closed :
    ∀ litex_function_args, litex_function_args.length = into_builder_spec.arity →
      into_builder_spec.requirements litex_function_args →
      Litex.In (into_builder_body litex_function_args) (into_builder_spec.range litex_function_args) :=
by
  intro litex_function_args litex_function_length litex_function_requirements
  change Litex.In (Litex.arg litex_function_args 0) Litex.R at litex_function_requirements
  change Litex.In (Litex.arg litex_function_args 0) (Litex.setBuilder Litex.R (fun litex_set_builder_9 => litex_set_builder_9 = litex_set_builder_9))
  exact (Litex.inSetBuilder_iff.mpr (And.intro (litex_function_requirements) ((rfl))))

noncomputable def into_builder_implementation : Litex.Object :=
  Litex.functionObject into_builder_spec into_builder_body into_builder_closed

noncomputable def into_builder : Litex.Object := into_builder_implementation

theorem fact40 : Litex.In into_builder (Litex.FnSet ({ arity := 1, requirements := fun litex_args_0 => Litex.In (Litex.arg litex_args_0 0) Litex.R, range := fun litex_args_0 => (Litex.setBuilder Litex.R (fun litex_set_builder_9 => litex_set_builder_9 = litex_set_builder_9)) } : Litex.FnSpec)) := by
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
  exact Litex.fnSetApplicable fact40 rfl (by simpa [Litex.arg] using (well_defined_fact_6))

noncomputable def obj_52 : Litex.Object :=
  into_builder [obj_32] (obj_52_applicable)

theorem obj_52_result : Litex.In obj_52 (Litex.setBuilder Litex.R (fun litex_set_builder_9 => litex_set_builder_9 = litex_set_builder_9)) :=
by
  simpa [obj_52] using (Litex.fnSetResult fact40 rfl (by simpa [Litex.arg] using (well_defined_fact_6)))

theorem fact42 : obj_52 = 1 := by
  exact (by
  change (into_builder [1] (obj_52_applicable)) = 1
  simp only [fact41, into_builder_implementation, into_builder_body, Litex.functionObject_apply, Litex.arg, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil])
```
<!-- END ACTUAL GENERATED LEAN: statement_object_interactions -->

These reuse the basis interfaces; no interaction-specific axiom or escape
hatch is introduced.

The generated file must contain the chosen witness, named-function replay,
the named theorem's local case proof, and `Litex.inSetBuilder_iff.mpr` in one
shared scope. Focused gates: `statement_object_interaction_probes_compile_together`
and `statement_object_interaction_probes_compile_with_mathlib`.

## Whole-ledger gates

```text
cargo test --release universal_examples_compile_to_the_new_abi -- --nocapture
LITEX_LEAN_PROJECT=/absolute/path/to/mathlib LITEX_LAKE=/absolute/path/to/lake cargo test --release universal_examples_compile_with_mathlib -- --ignored --nocapture
cargo test --release run_examples -- --nocapture
```
