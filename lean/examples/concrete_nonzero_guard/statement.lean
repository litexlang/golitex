import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_concrete_x5f_nonzero_x5f_guard_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

def prop_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) : Prop :=
  ∃ (h_2 : Litex.In _value_i1 (Litex.R (M := M))), ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))

noncomputable def _object_i3 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (¬ (_raw_i4 = (M.number (0 : ℂ)))))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by
  intro _raw_i4 h_33 h_3
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_33)
  have h_33 : Litex.In _value_i4 (Litex.R (M := M)) := h_33
  have h_3 : ((prop_1 (M := M)) _value_i4) :=
    (by
      change (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (¬ (_raw_i4 = (M.number (0 : ℂ)))))
      exact h_3)
  have h_34 : Litex.In _value_i4 (Litex.R (M := M)) :=
    (by rcases h_3 with ⟨h_2, h_1⟩; exact h_2)
  have h_37 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
    (by rcases h_3 with ⟨h_2, h_1⟩; exact h_1)
  change Litex.In (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_33) h_37) (Litex.R (M := M))
  exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (1 : ℂ) (1 : ℝ) (by norm_num))) h_33 ((Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_33) h_37)).wd.2.2)))
theorem h_111 : Litex.In (_object_i3 (M := M)) (by
  have _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (¬ (_raw_i4 = (M.number (0 : ℂ)))))) _raw_i4) → True := by
    intro _raw_i4 h_106 h_3
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_106)
    have h_106 : Litex.In _value_i4 (Litex.R (M := M)) := h_106
    have h_3 : ((prop_1 (M := M)) _value_i4) :=
      (by
        change (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (¬ (_raw_i4 = (M.number (0 : ℂ)))))
        exact h_3)
    have h_107 : Litex.In _value_i4 (Litex.R (M := M)) :=
      (by rcases h_3 with ⟨h_2, h_1⟩; exact h_2)
    have h_110 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
      (by rcases h_3 with ⟨h_2, h_1⟩; exact h_1)
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (¬ (_raw_i4 = (M.number (0 : ℂ)))))))) :=
  (Litex.formulaFnInFnSet (_object_i3 (M := M)))
theorem h_112 : Litex.Same (_object_i3 (M := M)) (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (¬ (_raw_i4 = (M.number (0 : ℂ)))))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by
  intro _raw_i4 h_33 h_3
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_33)
  have h_33 : Litex.In _value_i4 (Litex.R (M := M)) := h_33
  have h_3 : ((prop_1 (M := M)) _value_i4) :=
    (by
      change (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (¬ (_raw_i4 = (M.number (0 : ℂ)))))
      exact h_3)
  have h_34 : Litex.In _value_i4 (Litex.R (M := M)) :=
    (by rcases h_3 with ⟨h_2, h_1⟩; exact h_2)
  have h_37 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
    (by rcases h_3 with ⟨h_2, h_1⟩; exact h_1)
  change Litex.In (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_33) h_37) (Litex.R (M := M))
  exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (1 : ℂ) (1 : ℝ) (by norm_num))) h_33 ((Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_33) h_37)).wd.2.2))) :=
  (Litex.sameRefl (_object_i3 (M := M)))

theorem h_113 : ((prop_1 (M := M)) (Litex.number (M := M) (2 : ℂ))) :=
  (Exists.intro (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num))) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_118 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
  (by rcases (h_113 (M := M)) with ⟨h_2, h_1⟩; exact h_2)

theorem h_120 : ¬ Litex.Same (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
  (by rcases (h_113 (M := M)) with ⟨h_2, h_1⟩; exact h_1)

theorem h_121 : Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (¬ (_raw_i4 = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_111 (M := M)) (h_118 (M := M)) (h_113 (M := M))) (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (h_120 (M := M))) :=
  (((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.number (2 : ℂ))))).trans (by
    let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (¬ (_raw_i4 = (M.number (0 : ℂ)))))) (_object_i3 (M := M)) (Litex.number (M := M) (2 : ℂ)) (h_111 (M := M)) (h_118 (M := M)) (h_113 (M := M)))
    let _litex_literal := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (¬ (_raw_i4 = (M.number (0 : ℂ)))))) (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (¬ (_raw_i4 = (M.number (0 : ℂ)))))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by
      intro _raw_i4 h_33 h_3
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_33)
      have h_33 : Litex.In _value_i4 (Litex.R (M := M)) := h_33
      have h_3 : ((prop_1 (M := M)) _value_i4) :=
        (by
          change (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (¬ (_raw_i4 = (M.number (0 : ℂ)))))
          exact h_3)
      have h_34 : Litex.In _value_i4 (Litex.R (M := M)) :=
        (by rcases h_3 with ⟨h_2, h_1⟩; exact h_2)
      have h_37 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
        (by rcases h_3 with ⟨h_2, h_1⟩; exact h_1)
      change Litex.In (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_33) h_37) (Litex.R (M := M))
      exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (1 : ℂ) (1 : ℝ) (by norm_num))) h_33 ((Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_33) h_37)).wd.2.2))) (Litex.number (M := M) (2 : ℂ)) (Litex.formulaFnInFnSet (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (¬ (_raw_i4 = (M.number (0 : ℂ)))))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by
      intro _raw_i4 h_33 h_3
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_33)
      have h_33 : Litex.In _value_i4 (Litex.R (M := M)) := h_33
      have h_3 : ((prop_1 (M := M)) _value_i4) :=
        (by
          change (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (¬ (_raw_i4 = (M.number (0 : ℂ)))))
          exact h_3)
      have h_34 : Litex.In _value_i4 (Litex.R (M := M)) :=
        (by rcases h_3 with ⟨h_2, h_1⟩; exact h_2)
      have h_37 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
        (by rcases h_3 with ⟨h_2, h_1⟩; exact h_1)
      change Litex.In (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_33) h_37) (Litex.R (M := M))
      exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (1 : ℂ) (1 : ℝ) (by norm_num))) h_33 ((Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_33) h_37)).wd.2.2)))) (h_118 (M := M)) (h_113 (M := M)))
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (((Litex.sameRefl (_object_i3 (M := M)))).trans (h_112 (M := M))) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (¬ (_raw_i4 = (M.number (0 : ℂ)))))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (∃ (_predicate_witness : (M.mem _raw_i4 (M.standard Litex.StandardSetValue.real))), (¬ (_raw_i4 = (M.number (0 : ℂ)))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) from rfl))
  ))).trans (Litex.sameRefl (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (h_120 (M := M)))))
end LitexCompiled.file_lean_x2f_examples_x2f_concrete_x5f_nonzero_x5f_guard_x2f_statement_x2e_lit
