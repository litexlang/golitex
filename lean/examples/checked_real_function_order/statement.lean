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
      let _sign_binary := _atomic_wd_2_0
      exact Litex.addPositive _sign_binary.val.left _sign_binary.val.right _sign_binary.wd.1 _sign_binary.wd.2 ((by
      have _sign_real := h_15
      exact h_2
    )) (((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((M.real_members _).mpr ⟨(0 : ℝ), ((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))⟩) ((M.real_members _).mpr ⟨(1 : ℝ), ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))⟩)).mpr (by
      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) ((M.real_members _).mpr ⟨(0 : ℝ), ((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))⟩) = (0 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) ((M.real_members _).mpr ⟨(0 : ℝ), ((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))⟩)).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) ((M.real_members _).mpr ⟨(1 : ℝ), ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))⟩) = (1 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) ((M.real_members _).mpr ⟨(1 : ℝ), ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))⟩)).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
    ))))
  let _atomic_wd_1_1 := _atomic_wd_1_0
  exact Litex.Le _atomic_wd_1_1 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_14 _Host_i3 _rep_i3 _value_i3 h_15 h_2
          have h_673 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r < _s)) _raw_i2) → True := (by
              intro _raw_i2 h_664 h_1
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_664)
              have h_664 : Litex.In _value_i2 (Litex.R (M := M)) := h_664
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
          have h_674 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_15
                )
            )
          exact (by
            let _atomic_wd_1_0 := (let _object_w15 := (Litex.add _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_674) (Litex.numberInC (M := M) (1 : ℂ)));
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r < _s)) _value_i1 _object_w15 h_673 (by
              let _atomic_wd_2_0 := _object_w15
              exact (Litex.addInR _value_i3 (Litex.number (M := M) (1 : ℂ)) h_674 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))) (by
              let _atomic_wd_2_0 := _object_w15
              exact (by
                let _sign_binary := _atomic_wd_2_0
                exact Litex.addPositive _sign_binary.val.left _sign_binary.val.right _sign_binary.wd.1 _sign_binary.wd.2 ((by
                have _sign_real := h_674
                exact h_2
              )) (((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) ((M.real_members _).mpr ⟨(0 : ℝ), ((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))⟩) ((M.real_members _).mpr ⟨(1 : ℝ), ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))⟩)).mpr (by
                have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) ((M.real_members _).mpr ⟨(0 : ℝ), ((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))⟩) = (0 : ℝ) := by
                  apply Complex.ofReal_injective
                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) ((M.real_members _).mpr ⟨(0 : ℝ), ((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))⟩)).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) ((M.real_members _).mpr ⟨(1 : ℝ), ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))⟩) = (1 : ℝ) := by
                  apply Complex.ofReal_injective
                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) ((M.real_members _).mpr ⟨(1 : ℝ), ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))⟩)).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_left_value _litex_right_value) (by norm_num))))
              ))))
            let _atomic_wd_1_1 := _atomic_wd_1_0
            exact (Litex.leRefl _atomic_wd_1_1 (by
              let _atomic_wd_2_0 := _atomic_wd_1_1
              exact (by
                let _litex_return_call := _atomic_wd_2_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)))))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_checked_x5f_real_x5f_function_x5f_order_x2f_statement_x2e_lit
