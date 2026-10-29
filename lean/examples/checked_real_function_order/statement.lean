import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_checked_x5f_real_x5f_function_x5f_order_x2f_statement_x2e_lit

universe u v1 v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_14 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r < _s)) _raw_i2) → True := (by
    intro _raw_i2 h_5 h_1
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_5)
    have h_5 : Litex.In _value_i2 (Litex.R (M := M)) := h_5
    have h_1 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r < _s)
              exact h_1)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r < _s))))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_15 : Litex.In _value_i3 (Litex.R (M := M))) (h_2 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3), (by
  let _atomic_wd_1_0 := (let _object_w6 := (Litex.add _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_15) (Litex.numberInC (M := M) (1 : ℂ)));
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r < _s)) _value_i1 _object_w6 h_14 (by
    let _atomic_wd_2_0 := _object_w6
    exact (Litex.addInR _value_i3 (Litex.number (M := M) (1 : ℂ)) h_15 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))) (by
    let _atomic_wd_2_0 := _object_w6
    exact (by
      let _litex_positive_result := _atomic_wd_2_0
      exact Litex.addPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2 h_2 ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_right_value _litex_left_value) (by norm_num)))
    ))))
  let _atomic_wd_1_1 := _atomic_wd_1_0
  exact Litex.Le _atomic_wd_1_1 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_14 _Host_i3 _rep_i3 _value_i3 h_15 h_2
          have h_440 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r < _s)) _raw_i2) → True := (by
              intro _raw_i2 h_431 h_1
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_431)
              have h_431 : Litex.In _value_i2 (Litex.R (M := M)) := h_431
              have h_1 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r < _s)
                        exact h_1)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r < _s)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_14
                )
            )
          have h_441 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_15
                )
            )
          exact (by
            let _atomic_wd_1_0 := (let _object_w14 := (Litex.add _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_441) (Litex.numberInC (M := M) (1 : ℂ)));
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r < _s)) _value_i1 _object_w14 h_440 (by
              let _atomic_wd_2_0 := _object_w14
              exact (Litex.addInR _value_i3 (Litex.number (M := M) (1 : ℂ)) h_441 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))) (by
              let _atomic_wd_2_0 := _object_w14
              exact (by
                let _litex_positive_result := _atomic_wd_2_0
                exact Litex.addPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2 h_2 ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
                have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                  apply Complex.ofReal_injective
                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                  apply Complex.ofReal_injective
                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_right_value _litex_left_value) (by norm_num)))
              ))))
            let _atomic_wd_1_1 := _atomic_wd_1_0
            exact (Litex.leRefl _atomic_wd_1_1 (Litex.callInOutput _atomic_wd_1_1)))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_checked_x5f_real_x5f_function_x5f_order_x2f_statement_x2e_lit
