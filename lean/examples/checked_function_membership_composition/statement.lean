import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_checked_x5f_function_x5f_membership_x5f_composition_x2f_statement_x2e_lit

universe u v1 v3 v5 v7 v9 v10 v12
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
  let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _object_w6 := (Litex.add _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_15) (Litex.numberInC (M := M) (1 : ℂ)));
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
    ))));
  let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
  (Litex.add _wd_2_0 _wd_2_1 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.realToComplex _atomic_wd_2_0 (Litex.callInOutput _atomic_wd_2_0))) (Litex.numberInC (M := M) (1 : ℂ))));
  let _wd_1_1 := (let _wd_2_0 := (_wd_1_0).val.left;
  let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
  (Litex.sub _wd_2_0 _wd_2_1 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.realToComplex _atomic_wd_2_0 (Litex.callInOutput _atomic_wd_2_0))) (Litex.numberInC (M := M) (1 : ℂ))));
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_2_0 := _wd_1_0
    exact (Litex.addInC (_atomic_wd_2_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex (_atomic_wd_2_0).val.left (Litex.callInOutput (_atomic_wd_2_0).val.left)) (Litex.numberInC (M := M) (1 : ℂ)))) (by
    let _atomic_wd_2_0 := _wd_1_1
    exact (Litex.subInC (_atomic_wd_2_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex (_atomic_wd_2_0).val.left (Litex.callInOutput (_atomic_wd_2_0).val.left)) (Litex.numberInC (M := M) (1 : ℂ))))))
  exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_14 _Host_i3 _rep_i3 _value_i3 h_15 h_2
          have h_1403 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i2 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r < _s)) _raw_i2) → True := (by
              intro _raw_i2 h_1394 h_1
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1394)
              have h_1394 : Litex.In _value_i2 (Litex.R (M := M)) := h_1394
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
          have h_1404 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_15
                )
            )
          exact (by
            let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _object_w19 := (Litex.add _value_i3 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_1404) (Litex.numberInC (M := M) (1 : ℂ)));
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i2 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i2 = M.number (_s : ℂ) ∧ _r < _s)) _value_i1 _object_w19 h_1403 (by
              let _atomic_wd_2_0 := _object_w19
              exact (Litex.addInR _value_i3 (Litex.number (M := M) (1 : ℂ)) h_1404 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))) (by
              let _atomic_wd_2_0 := _object_w19
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
              ))));
            let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
            (Litex.add _wd_2_0 _wd_2_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              exact (Litex.realToComplex _atomic_wd_2_0 (Litex.callInOutput _atomic_wd_2_0))) (Litex.numberInC (M := M) (1 : ℂ))));
            let _wd_1_1 := (let _wd_2_0 := (_wd_1_0).val.left;
            let _wd_2_1 := (Litex.number (M := M) (1 : ℂ));
            (Litex.sub _wd_2_0 _wd_2_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              exact (Litex.realToComplex _atomic_wd_2_0 (Litex.callInOutput _atomic_wd_2_0))) (Litex.numberInC (M := M) (1 : ℂ))));
            (Litex.mul _wd_1_0 _wd_1_1 (by
              let _atomic_wd_2_0 := _wd_1_0
              exact (Litex.addInC (_atomic_wd_2_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex (_atomic_wd_2_0).val.left (Litex.callInOutput (_atomic_wd_2_0).val.left)) (Litex.numberInC (M := M) (1 : ℂ)))) (by
              let _atomic_wd_2_0 := _wd_1_1
              exact (Litex.subInC (_atomic_wd_2_0).val.left (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex (_atomic_wd_2_0).val.left (Litex.callInOutput (_atomic_wd_2_0).val.left)) (Litex.numberInC (M := M) (1 : ℂ))))))
            exact (Litex.mulInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.addInR ((_atomic_wd_1_0).val.left).val.left (Litex.number (M := M) (1 : ℂ)) (by
              let _litex_return_call := ((_atomic_wd_1_0).val.left).val.left
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))) (Litex.subInR ((_atomic_wd_1_0).val.left).val.left (Litex.number (M := M) (1 : ℂ)) (by
              let _litex_return_call := ((_atomic_wd_1_0).val.left).val.left
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))))
        )
      )
  )

theorem h_4339 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_4349 : Litex.In _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i6 = M.number (_s : ℂ) ∧ _r < _s)) _raw_i6) → True := (by
    intro _raw_i6 h_4340 h_4336
    let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_4340)
    have h_4340 : Litex.In _value_i6 (Litex.R (M := M)) := h_4340
    have h_4336 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i6 = M.number (_s : ℂ) ∧ _r < _s)
              exact h_4336)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i6 = M.number (_s : ℂ) ∧ _r < _s))))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_4350 : Litex.In _value_i7 (Litex.R (M := M))) (h_4337 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i7), (by
  let _atomic_wd_1_0 := (let _wd_1_0 := (let _object_w45 := (Litex.add _value_i7 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_4350) (Litex.numberInC (M := M) (1 : ℂ)));
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i6 = M.number (_s : ℂ) ∧ _r < _s)) _value_i5 _object_w45 h_4349 (by
    let _atomic_wd_2_0 := _object_w45
    exact (Litex.addInR _value_i7 (Litex.number (M := M) (1 : ℂ)) h_4350 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))) (by
    let _atomic_wd_2_0 := _object_w45
    exact (by
      let _litex_positive_result := _atomic_wd_2_0
      exact Litex.addPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2 h_4337 ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_right_value _litex_left_value) (by norm_num)))
    ))));
  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_2_0 := _wd_1_0
    exact (Litex.realToComplex _atomic_wd_2_0 (Litex.callInOutput _atomic_wd_2_0))) (Litex.numberInC (M := M) (1 : ℂ))))
  let _atomic_wd_1_1 := _atomic_wd_1_0
  exact Litex.Le _atomic_wd_1_1 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_4349 _Host_i7 _rep_i7 _value_i7 h_4350 h_4337
          have h_5426 : Litex.In _value_i5 (let _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i6 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i6 = M.number (_s : ℂ) ∧ _r < _s)) _raw_i6) → True := (by
              intro _raw_i6 h_5417 h_4336
              let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_5417)
              have h_5417 : Litex.In _value_i6 (Litex.R (M := M)) := h_5417
              have h_4336 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i6 :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i6 = M.number (_s : ℂ) ∧ _r < _s)
                        exact h_4336)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i6 = M.number (_s : ℂ) ∧ _r < _s)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_4349
                )
            )
          have h_5427 : Litex.In _value_i7 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_4350
                )
            )
          exact (by
            let _atomic_wd_1_0 := (let _wd_1_0 := (let _object_w58 := (Litex.add _value_i7 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_5427) (Litex.numberInC (M := M) (1 : ℂ)));
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i6 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i6 = M.number (_s : ℂ) ∧ _r < _s)) _value_i5 _object_w58 h_5426 (by
              let _atomic_wd_2_0 := _object_w58
              exact (Litex.addInR _value_i7 (Litex.number (M := M) (1 : ℂ)) h_5427 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))) (by
              let _atomic_wd_2_0 := _object_w58
              exact (by
                let _litex_positive_result := _atomic_wd_2_0
                exact Litex.addPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2 h_4337 ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
                have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                  apply Complex.ofReal_injective
                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                  apply Complex.ofReal_injective
                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_right_value _litex_left_value) (by norm_num)))
              ))));
            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
            (Litex.add _wd_1_0 _wd_1_1 (by
              let _atomic_wd_2_0 := _wd_1_0
              exact (Litex.realToComplex _atomic_wd_2_0 (Litex.callInOutput _atomic_wd_2_0))) (Litex.numberInC (M := M) (1 : ℂ))))
            let _atomic_wd_1_1 := _atomic_wd_1_0
            exact (Litex.leRefl _atomic_wd_1_1 (Litex.addInR (_atomic_wd_1_1).val.left (Litex.number (M := M) (1 : ℂ)) (by
              let _litex_return_call := (_atomic_wd_1_1).val.left
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))))
        )
      )
  )

theorem h_7577 : ∀ {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_7579 : Litex.In _value_i9 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_7594 : Litex.In _value_i10 (let _checked_header : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i11 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i11 = M.number (_s : ℂ) ∧ _r < _s)) _raw_i11) → True := (by
    intro _raw_i11 h_7581 h_7573
    let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_7581)
    have h_7581 : Litex.In _value_i11 (Litex.R (M := M)) := h_7581
    have h_7573 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i11 :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i11 = M.number (_s : ℂ) ∧ _r < _s)
              exact h_7573)
          )
      )
    exact True.intro);
  Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i11 = M.number (_s : ℂ) ∧ _r < _s))))) {_Host_i12 : Type v12} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_7595 : Litex.In _value_i12 (Litex.R (M := M))) (h_7574 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i12) (h_7575 : (by
  let _atomic_wd_1_1 := (let _wd_1_0 := (let _object_w86 := (Litex.add _value_i12 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_7595) (Litex.numberInC (M := M) (1 : ℂ)));
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i11 = M.number (_s : ℂ) ∧ _r < _s)) _value_i10 _object_w86 h_7594 (by
    let _atomic_wd_2_0 := _object_w86
    exact (Litex.addInR _value_i12 (Litex.number (M := M) (1 : ℂ)) h_7595 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))) (by
    let _atomic_wd_2_0 := _object_w86
    exact (by
      let _litex_positive_result := _atomic_wd_2_0
      exact Litex.addPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2 h_7574 ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_right_value _litex_left_value) (by norm_num)))
    ))));
  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_2_0 := _wd_1_0
    exact (Litex.realToComplex _atomic_wd_2_0 (Litex.callInOutput _atomic_wd_2_0))) (Litex.numberInC (M := M) (1 : ℂ))))
  have _sequence_domain : Litex.In _value_i9 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i9 _value_i9 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_7579)
  have _sequence_limit_real : Litex.In _atomic_wd_1_1 (Litex.R (M := M)) := (Litex.addInR (_atomic_wd_1_1).val.left (Litex.number (M := M) (1 : ℂ)) (by
    let _litex_return_call := (_atomic_wd_1_1).val.left
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callInOutput _litex_return_call)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))
  exact Litex.HasSequenceLimit _value_i9 _atomic_wd_1_1)), (by
  let _atomic_wd_1_1 := (let _wd_1_0 := (let _object_w86 := (Litex.add _value_i12 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_7595) (Litex.numberInC (M := M) (1 : ℂ)));
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i11 = M.number (_s : ℂ) ∧ _r < _s)) _value_i10 _object_w86 h_7594 (by
    let _atomic_wd_1_0 := _object_w86
    exact (Litex.addInR _value_i12 (Litex.number (M := M) (1 : ℂ)) h_7595 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))) (by
    let _atomic_wd_1_0 := _object_w86
    exact (by
      let _litex_positive_result := _atomic_wd_1_0
      exact Litex.addPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2 h_7574 ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
      have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
      have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
        apply Complex.ofReal_injective
        exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
      exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_right_value _litex_left_value) (by norm_num)))
    ))));
  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (Litex.numberInC (M := M) (1 : ℂ))))
  exact Litex.HasSequenceLimit _value_i9 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i9 _rep_i9 _value_i9 h_7579 _Host_i10 _rep_i10 _value_i10 h_7594 _Host_i12 _rep_i12 _value_i12 h_7595 h_7574 h_7575
          let _object_h7580 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_7580 : Litex.In _value_i9 _object_h7580 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i9 _value_i9 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h7580 (Litex.sameRefl _value_i9) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_7579)
                )
            )
          have h_8167 : Litex.In _value_i9 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_7579
                )
            )
          have h_8182 : Litex.In _value_i10 (let _checked_header : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (M.standard Litex.StandardSetValue.real) → ((fun (_raw_i11 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i11 = M.number (_s : ℂ) ∧ _r < _s)) _raw_i11) → True := (by
              intro _raw_i11 h_8169 h_7573
              let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_8169)
              have h_8169 : Litex.In _value_i11 (Litex.R (M := M)) := h_8169
              have h_7573 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i11 :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        change (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i11 = M.number (_s : ℂ) ∧ _r < _s)
                        exact h_7573)
                    )
                )
              exact True.intro);
            Litex.fnSet (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i11 = M.number (_s : ℂ) ∧ _r < _s)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_7594
                )
            )
          have h_8183 : Litex.In _value_i12 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_7595
                )
            )
          let _object_h8168 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_8168 : Litex.In _value_i9 _object_h8168 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i9 _value_i9 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h8168 (Litex.sameRefl _value_i9) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_8167)
                )
            )
          exact (by
            let _atomic_wd_1_1 := (let _wd_1_0 := (let _object_w96 := (Litex.add _value_i12 (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ h_8183) (Litex.numberInC (M := M) (1 : ℂ)));
            (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i11 : M.Value) => (∃ (_r _s : ℝ), (M.number (0 : ℂ)) = M.number (_r : ℂ) ∧ _raw_i11 = M.number (_s : ℂ) ∧ _r < _s)) _value_i10 _object_w96 h_8182 (by
              let _atomic_wd_1_0 := _object_w96
              exact (Litex.addInR _value_i12 (Litex.number (M := M) (1 : ℂ)) h_8183 (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))) (by
              let _atomic_wd_1_0 := _object_w96
              exact (by
                let _litex_positive_result := _atomic_wd_1_0
                exact Litex.addPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2 h_7574 ((Litex.NativeBridge.lt_iff_asReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).mpr (by
                have _litex_left_value : Litex.NativeBridge.asReal (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)) = (1 : ℝ) := by
                  apply Complex.ofReal_injective
                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))))
                have _litex_right_value : Litex.NativeBridge.asReal (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) = (0 : ℝ) := by
                  apply Complex.ofReal_injective
                  exact M.number_injective ((Litex.NativeBridge.asReal_spec (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))).symm.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num))))
                exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r < _litex_s) _litex_right_value _litex_left_value) (by norm_num)))
              ))));
            let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
            (Litex.add _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callInOutput _atomic_wd_1_0))) (Litex.numberInC (M := M) (1 : ℂ))))
            exact h_7575)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_checked_x5f_function_x5f_membership_x5f_composition_x2f_statement_x2e_lit
