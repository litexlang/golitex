import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_reciprocal_x5f_product_x5f_and_x5f_evaluation_x2f_statement_x2e_lit

universe u v1 v6
variable {M : Litex.Semantics.{u}}
variable [_functionSemantics : Litex.FunctionSemantics M]

def prop_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) : Prop :=
  ∃ (h_2 : Litex.In _value_i1 (Litex.R (M := M))), ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ))

noncomputable def _object_i3 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by
  intro _raw_i4 h_45 h_3
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_45)
  have h_45 : Litex.In _value_i4 (Litex.R (M := M)) := h_45
  have h_3 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      change (¬ (_raw_i4 = (M.number (0 : ℂ))))
      exact h_3)
  change Litex.In (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_45) h_3) (Litex.R (M := M))
  exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (1 : ℂ) (1 : ℝ) (by norm_num))) h_45 ((Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_45) h_3)).wd.2.2)))
theorem h_94 : Litex.In (_object_i3 (M := M)) (by
  have _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := by
    intro _raw_i4 h_93 h_3
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_93)
    have h_93 : Litex.In _value_i4 (Litex.R (M := M)) := h_93
    have h_3 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        change (¬ (_raw_i4 = (M.number (0 : ℂ))))
        exact h_3)
    exact True.intro
  exact Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))))) :=
  (Litex.formulaFnInFnSet (_object_i3 (M := M)))
theorem h_95 : Litex.Same (_object_i3 (M := M)) (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by
  intro _raw_i4 h_45 h_3
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_45)
  have h_45 : Litex.In _value_i4 (Litex.R (M := M)) := h_45
  have h_3 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      change (¬ (_raw_i4 = (M.number (0 : ℂ))))
      exact h_3)
  change Litex.In (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_45) h_3) (Litex.R (M := M))
  exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (1 : ℂ) (1 : ℝ) (by norm_num))) h_45 ((Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_45) h_3)).wd.2.2))) :=
  (Litex.sameRefl (_object_i3 (M := M)))

theorem h_98 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_222 : Litex.In _value_i6 (Litex.R (M := M))) (h_96 : ((prop_1 (M := M)) _value_i6)), (let h_226 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
  (by rcases h_96 with ⟨h_2, h_1⟩; exact h_1);
Litex.Same (Litex.mul (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) _value_i6 (h_94 (M := M)) h_222 h_226) _value_i6 (Litex.realToComplex (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) _value_i6 (h_94 (M := M)) h_222 h_226) (Litex.callInOutput (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) _value_i6 (h_94 (M := M)) h_222 h_226))) (Litex.realToComplex _value_i6 h_222)) (Litex.number (M := M) (1 : ℂ))) :=
  (by
    intro _Host_i6 _rep_i6 _value_i6 h_222 h_96
    have h_223 : Litex.In _value_i6 (Litex.R (M := M)) :=
      (by rcases h_96 with ⟨h_2, h_1⟩; exact h_2)
    have h_226 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
      (by rcases h_96 with ⟨h_2, h_1⟩; exact h_1)
    have h_99 : Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) _value_i6 (h_94 (M := M)) h_222 h_226) (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_222) h_226) :=
      (((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.denote _value_i6)))).trans (by
        let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) _value_i6 (h_94 (M := M)) h_222 h_226)
        let _litex_literal := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by
          intro _raw_i4 h_45 h_3
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_45)
          have h_45 : Litex.In _value_i4 (Litex.R (M := M)) := h_45
          have h_3 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              change (¬ (_raw_i4 = (M.number (0 : ℂ))))
              exact h_3)
          change Litex.In (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_45) h_3) (Litex.R (M := M))
          exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (1 : ℂ) (1 : ℝ) (by norm_num))) h_45 ((Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_45) h_3)).wd.2.2))) _value_i6 (Litex.formulaFnInFnSet (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by
          intro _raw_i4 h_45 h_3
          let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_45)
          have h_45 : Litex.In _value_i4 (Litex.R (M := M)) := h_45
          have h_3 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              change (¬ (_raw_i4 = (M.number (0 : ℂ))))
              exact h_3)
          change Litex.In (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_45) h_3) (Litex.R (M := M))
          exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (1 : ℂ) (1 : ℝ) (by norm_num))) h_45 ((Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_45) h_3)).wd.2.2)))) h_222 h_226)
        have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (((Litex.sameRefl (_object_i3 (M := M)))).trans (h_95 (M := M))) (Litex.sameRefl _litex_original.val.argument)
        have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
        exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i6)) from rfl))
      ))).trans (Litex.sameRefl (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_222) h_226)))
    have h_100 : Litex.Same (Litex.mul (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) _value_i6 (h_94 (M := M)) h_222 h_226) _value_i6 (Litex.realToComplex (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) _value_i6 (h_94 (M := M)) h_222 h_226) (Litex.callInOutput (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) _value_i6 (h_94 (M := M)) h_222 h_226))) (Litex.realToComplex _value_i6 h_222)) (Litex.mul (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_222) h_226) _value_i6 (Litex.divInC (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_222) ((Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_222) h_226)).wd.2.2) (Litex.realToComplex _value_i6 h_222)) :=
      (congrArg₂ M.mulValue (((Litex.sameRefl (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) _value_i6 (h_94 (M := M)) h_222 h_226))).trans h_99) (Litex.sameRefl _value_i6))
    have h_101 : Litex.Same (Litex.mul (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_222) h_226) _value_i6 (Litex.divInC (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_222) ((Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_222) h_226)).wd.2.2) (Litex.realToComplex _value_i6 h_222)) (Litex.number (M := M) (1 : ℂ)) :=
      (Litex.NativeBridge.sameOfDenoteNumber (Litex.mul (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_222) h_226) _value_i6 (Litex.divInC (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_222) ((Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_222) h_226)).wd.2.2) (Litex.realToComplex _value_i6 h_222)) (Litex.number (M := M) (1 : ℂ)) (((1 : ℂ) / (Litex.NativeBridge.asComplex _value_i6 (Litex.realToComplex _value_i6 h_222))) * (Litex.NativeBridge.asComplex _value_i6 (Litex.realToComplex _value_i6 h_222))) (1 : ℂ) (Litex.NativeBridge.denoteMul (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_222) h_226) _value_i6 (Litex.divInC (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_222) ((Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_222) h_226)).wd.2.2) (Litex.realToComplex _value_i6 h_222) ((1 : ℂ) / (Litex.NativeBridge.asComplex _value_i6 (Litex.realToComplex _value_i6 h_222))) (Litex.NativeBridge.asComplex _value_i6 (Litex.realToComplex _value_i6 h_222)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_222) h_226 (1 : ℂ) (Litex.NativeBridge.asComplex _value_i6 (Litex.realToComplex _value_i6 h_222)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.realToComplex _value_i6 h_222))) (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.realToComplex _value_i6 h_222))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (((div_eq_iff (Litex.NativeBridge.nativeNonzeroOfDenote _value_i6 (Litex.NativeBridge.asComplex _value_i6 (Litex.realToComplex _value_i6 h_222)) (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.realToComplex _value_i6 h_222)) ((Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_222) h_226)).wd.2.2)).mp (Litex.NativeBridge.nativeEqOfDenoteNumber (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_222) h_226) (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_222) h_226) ((1 : ℂ) / (Litex.NativeBridge.asComplex _value_i6 (Litex.realToComplex _value_i6 h_222))) ((1 : ℂ) / (Litex.NativeBridge.asComplex _value_i6 (Litex.realToComplex _value_i6 h_222))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_222) h_226 (1 : ℂ) (Litex.NativeBridge.asComplex _value_i6 (Litex.realToComplex _value_i6 h_222)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.realToComplex _value_i6 h_222))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_222) h_226 (1 : ℂ) (Litex.NativeBridge.asComplex _value_i6 (Litex.realToComplex _value_i6 h_222)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.realToComplex _value_i6 h_222))) (Litex.sameRefl (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i6 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i6 h_222) h_226)))).symm))
    exact (((((Litex.sameRefl (Litex.mul (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) _value_i6 (h_94 (M := M)) h_222 h_226) _value_i6 (Litex.realToComplex (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) _value_i6 (h_94 (M := M)) h_222 h_226) (Litex.callInOutput (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) _value_i6 (h_94 (M := M)) h_222 h_226))) (Litex.realToComplex _value_i6 h_222)))).trans h_100)).trans h_101)
  )

noncomputable def _object_i8 := (Litex.number (M := M) (2 : ℂ))
theorem h_894 : Litex.In (_object_i8 (M := M)) (Litex.R (M := M)) :=
  (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num)))
theorem h_895 : Litex.Same (_object_i8 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (Litex.sameRefl (Litex.number (M := M) (2 : ℂ)))

theorem h_896 : ((prop_1 (M := M)) (_object_i8 (M := M))) :=
  (Exists.intro (h_894 (M := M)) (Litex.notSameOfSame (Litex.number (M := M) (2 : ℂ)) (_object_i8 (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((h_895 (M := M))).symm (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))

theorem h_950 : Litex.In (_object_i8 (M := M)) (Litex.R (M := M)) :=
  (by rcases (h_896 (M := M)) with ⟨h_2, h_1⟩; exact h_2)

theorem h_954 : ¬ Litex.Same (_object_i8 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by rcases (h_896 (M := M)) with ⟨h_2, h_1⟩; exact h_1)

noncomputable def _object_i9 := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_894 (M := M)) (h_954 (M := M)))
theorem h_967 : Litex.Same (_object_i9 (M := M)) (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_894 (M := M)) (h_954 (M := M))) :=
  (Litex.sameRefl (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_894 (M := M)) (h_954 (M := M))))

theorem h_968 : Litex.Same (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_894 (M := M)) (h_954 (M := M))) (Litex.div (Litex.number (M := M) (1 : ℂ)) (_object_i8 (M := M)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex (_object_i8 (M := M)) (h_894 (M := M))) (h_954 (M := M))) :=
  (((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.denote (_object_i8 (M := M)))))).trans (by
    let _litex_original := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_894 (M := M)) (h_954 (M := M)))
    let _litex_literal := (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by
      intro _raw_i4 h_45 h_3
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_45)
      have h_45 : Litex.In _value_i4 (Litex.R (M := M)) := h_45
      have h_3 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          change (¬ (_raw_i4 = (M.number (0 : ℂ))))
          exact h_3)
      change Litex.In (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_45) h_3) (Litex.R (M := M))
      exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (1 : ℂ) (1 : ℝ) (by norm_num))) h_45 ((Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_45) h_3)).wd.2.2))) (_object_i8 (M := M)) (Litex.formulaFnInFnSet (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by
      intro _raw_i4 h_45 h_3
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_45)
      have h_45 : Litex.In _value_i4 (Litex.R (M := M)) := h_45
      have h_3 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
        (by
          change (¬ (_raw_i4 = (M.number (0 : ℂ))))
          exact h_3)
      change Litex.In (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_45) h_3) (Litex.R (M := M))
      exact (Litex.divInR (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (1 : ℂ) (1 : ℝ) (by norm_num))) h_45 ((Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i4 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex _value_i4 h_45) h_3)).wd.2.2)))) (h_894 (M := M)) (h_954 (M := M)))
    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (((Litex.sameRefl (_object_i3 (M := M)))).trans (h_95 (M := M))) (Litex.sameRefl _litex_original.val.argument)
    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i4 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i4)) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote (_object_i8 (M := M)))) from rfl))
  ))).trans (Litex.sameRefl (Litex.div (Litex.number (M := M) (1 : ℂ)) (_object_i8 (M := M)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex (_object_i8 (M := M)) (h_894 (M := M))) (h_954 (M := M)))))

theorem h_1522 : Litex.Same (Litex.div (Litex.number (M := M) (1 : ℂ)) (_object_i8 (M := M)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.realToComplex (_object_i8 (M := M)) (h_894 (M := M))) (h_954 (M := M))) (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.notSameOfSame (_object_i8 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (((Litex.sameRefl (_object_i8 (M := M)))).trans (h_895 (M := M))) (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) (h_954 (M := M)))) :=
  (congrArg₂ M.divValue (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))) (((Litex.sameRefl (_object_i8 (M := M)))).trans (h_895 (M := M))))

theorem h_1553 : (let h_1554 : Litex.In (_object_i8 (M := M)) (Litex.R (M := M)) :=
  (h_894 (M := M));
Litex.Same (Litex.mul (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_894 (M := M)) (h_954 (M := M))) (_object_i8 (M := M)) (Litex.realToComplex (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_894 (M := M)) (h_954 (M := M))) (Litex.callInOutput (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_894 (M := M)) (h_954 (M := M))))) (Litex.realToComplex (_object_i8 (M := M)) h_1554)) (Litex.number (M := M) (1 : ℂ))) :=
  (by
    have h_1554 : Litex.In (_object_i8 (M := M)) (Litex.R (M := M)) :=
      (h_894 (M := M))
    have h_1555 : ((prop_1 (M := M)) (_object_i8 (M := M))) :=
      (h_896 (M := M))
    have h_1556 : Litex.Same (Litex.mul (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_894 (M := M)) (h_954 (M := M))) (_object_i8 (M := M)) (Litex.realToComplex (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_894 (M := M)) (h_954 (M := M))) (Litex.callInOutput (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_894 (M := M)) (h_954 (M := M))))) (Litex.realToComplex (_object_i8 (M := M)) h_1554)) (Litex.number (M := M) (1 : ℂ)) :=
      ((h_98 (M := M)) (_object_i8 (M := M)) h_1554 h_1555)
    exact (((Litex.sameRefl (Litex.mul (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_894 (M := M)) (h_954 (M := M))) (_object_i8 (M := M)) (Litex.realToComplex (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_894 (M := M)) (h_954 (M := M))) (Litex.callInOutput (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) (_object_i3 (M := M)) (_object_i8 (M := M)) (h_94 (M := M)) (h_894 (M := M)) (h_954 (M := M))))) (Litex.realToComplex (_object_i8 (M := M)) h_1554)))).symm.trans ((h_1556).trans (Litex.sameRefl (Litex.number (M := M) (1 : ℂ)))))
  )

theorem h_1814 : Litex.Same (_object_i9 (M := M)) (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.notSameOfSame (_object_i8 (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (((Litex.sameRefl (_object_i8 (M := M)))).trans (h_895 (M := M))) (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) (h_954 (M := M)))) :=
  (((((((Litex.sameRefl (_object_i9 (M := M)))).trans (h_967 (M := M)))).trans (h_968 (M := M)))).trans (h_1522 (M := M)))
end LitexCompiled.file_lean_x2f_examples_x2f_reciprocal_x5f_product_x5f_and_x5f_evaluation_x2f_statement_x2e_lit
