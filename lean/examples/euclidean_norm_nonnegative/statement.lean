import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_euclidean_x5f_norm_x5f_nonnegative_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_12 : Litex.In _value_i2 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_4)), (by
  let _atomic_wd_1_1 := (Litex.euclideanNorm _value_i2 _value_i1 h_4 (by
    let _atomic_wd_2_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_4)
    exact h_12))
  exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_4 _Host_i2 _rep_i2 _value_i2 h_12
          have h_5 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_4)
                )
            )
          let _object_h13 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_4)))
          have h_13 : Litex.In _value_i2 _object_h13 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i2 _value_i2 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_4) _object_h13 (Litex.sameRefl _value_i2) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_4)) h_12)
                )
            )
          have h_61 : Litex.In _value_i1 (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_4
                )
            )
          have h_69 : Litex.In _value_i2 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61) :=
            (by
              litex_checked_step =>
                exact (
                  h_12
                )
            )
          have h_62 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_61)
                )
            )
          let _object_h70 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)))
          have h_70 : Litex.In _value_i2 _object_h70 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i2 _value_i2 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61) _object_h70 (Litex.sameRefl _value_i2) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)) h_69)
                )
            )
          have h_73 : Litex.Same (let _wd_1_0 := (Litex.euclideanNorm _value_i2 _value_i1 h_61 (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
            exact h_69));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := (Litex.euclideanNorm _value_i2 _value_i1 h_61 (by
              let _atomic_wd_2_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
              exact h_69))
            exact (Litex.euclideanNormInR _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_61));
          let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i6)) (M.number (2 : ℂ)))) _litex_input) (by
            have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_1_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i6)) (M.number (2 : ℂ)))) _raw_i6) (Litex.denote (Litex.R (M := M))) := (by
              intro _raw_i6 h_2036 _
              let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_2036)
              have h_2036 : Litex.In _value_i6 _wd_1_0 := h_2036
              have h_2037 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_2036).1
                    )
                )
              have h_2038 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_2036).2.1
                    )
                )
              have h_2039 : Litex.Le _value_i6 _value_i1 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_2036).2.2
                    )
                )
              have h_2040 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive _wd_1_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2036)
                    )
                )
              change (by
                let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i6;
                Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_70 (by
                  let _atomic_wd_2_1 := _wd_1_0
                  exact h_2036) True.intro);
                (Litex.complexAbs _wd_3_0 (by
                  let _atomic_wd_2_0 := _wd_3_0
                  exact (by
                    let _litex_return_call := _atomic_wd_2_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                  let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
                  (Litex.complexAbs _wd_3_0 (by
                    let _atomic_wd_3_0 := _wd_3_0
                    exact (by
                      let _litex_return_call := _atomic_wd_3_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                  exact (Litex.complexAbsInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
              exact (by
                let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i6;
                Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_70 (by
                  let _atomic_wd_2_1 := _wd_1_0
                  exact h_2036) True.intro);
                (Litex.complexAbs _wd_3_0 (by
                  let _atomic_wd_2_0 := _wd_3_0
                  exact (by
                    let _litex_return_call := _atomic_wd_2_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                  let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
                  (Litex.complexAbs _wd_3_0 (by
                    let _atomic_wd_3_0 := _wd_3_0
                    exact (by
                      let _litex_return_call := _atomic_wd_3_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                  exact (Litex.complexAbsInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                exact (by
                  let _litex_power := _atomic_wd_1_0
                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_1_0).val.base)
                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                )))
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
            exact _litex_checked_return _litex_input _litex_members _litex_guard));
          (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
            let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_61))
            exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
            let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_61))
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_61))
            exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_71 : Litex.In _value_i1 (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_61
                          )
                      )
                    have h_80 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.naturalNonnegative _value_i1 h_71)
                          )
                      )
                    have h_72 : (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                      exact Litex.In _value_i2 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                              exact h_69)
                          )
                      )
                    let _object_h89 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)))
                    have h_89 : Litex.In _value_i2 _object_h89 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inOfSame _value_i2 _value_i2 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61) _object_h89 (Litex.sameRefl _value_i2) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)) h_72)
                          )
                      )
                    exact (And.left (And.intro (show (by
                    let _equal_wd_1_0 := (let _wd_1_0 := (Litex.euclideanNorm _value_i2 _value_i1 h_71 (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                      exact h_72));
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                      let _atomic_wd_1_0 := (Litex.euclideanNorm _value_i2 _value_i1 h_71 (by
                        let _atomic_wd_2_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                        exact h_72))
                      exact (Litex.euclideanNormInR _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                    let _equal_wd_1_1 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_71));
                    let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i6)) (M.number (2 : ℂ)))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_1_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i6)) (M.number (2 : ℂ)))) _raw_i6) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i6 h_496 _
                        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_496)
                        have h_496 : Litex.In _value_i6 _wd_1_0 := h_496
                        have h_497 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_496).1
                              )
                          )
                        have h_498 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_496).2.1
                              )
                          )
                        have h_499 : Litex.Le _value_i6 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_496).2.2
                              )
                          )
                        have h_500 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_1_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_496)
                              )
                          )
                        change (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i6;
                          Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_89 (by
                            let _atomic_wd_2_1 := _wd_1_0
                            exact h_496) True.intro);
                          (Litex.complexAbs _wd_3_0 (by
                            let _atomic_wd_2_0 := _wd_3_0
                            exact (by
                              let _litex_return_call := _atomic_wd_2_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                            let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
                            (Litex.complexAbs _wd_3_0 (by
                              let _atomic_wd_3_0 := _wd_3_0
                              exact (by
                                let _litex_return_call := _atomic_wd_3_0
                                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                            exact (Litex.complexAbsInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                          exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i6;
                          Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_89 (by
                            let _atomic_wd_2_1 := _wd_1_0
                            exact h_496) True.intro);
                          (Litex.complexAbs _wd_3_0 (by
                            let _atomic_wd_2_0 := _wd_3_0
                            exact (by
                              let _litex_return_call := _atomic_wd_2_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                            let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
                            (Litex.complexAbs _wd_3_0 (by
                              let _atomic_wd_3_0 := _wd_3_0
                              exact (by
                                let _litex_return_call := _atomic_wd_3_0
                                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                            exact (Litex.complexAbsInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                          exact (by
                            let _litex_power := _atomic_wd_1_0
                            have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_1_0).val.base)
                            have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                            exact Litex.powStructuralInR _litex_power _recorded_power_base
                          )))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_71))
                      exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_71))
                      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_71))
                      exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) from (Litex.euclideanNormSquare (Litex.euclideanNorm _value_i2 _value_i1 h_71 (by
                    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                    exact h_72))).trans (congrArg M.number (Litex.euclideanNormSumFormula (Litex.euclideanNorm _value_i2 _value_i1 h_71 (by
                    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                    exact h_72)) ((let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_71));
                  let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i6)) (M.number (2 : ℂ)))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_1_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i6)) (M.number (2 : ℂ)))) _raw_i6) (Litex.denote (Litex.R (M := M))) := (by
                      intro _raw_i6 h_496 _
                      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_496)
                      have h_496 : Litex.In _value_i6 _wd_1_0 := h_496
                      have h_497 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_496).1
                            )
                        )
                      have h_498 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_496).2.1
                            )
                        )
                      have h_499 : Litex.Le _value_i6 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_496).2.2
                            )
                        )
                      have h_500 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_1_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_496)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i6;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_89 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_496) True.intro);
                        (Litex.complexAbs _wd_3_0 (by
                          let _atomic_wd_2_0 := _wd_3_0
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
                          (Litex.complexAbs _wd_3_0 (by
                            let _atomic_wd_3_0 := _wd_3_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i6;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_89 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_496) True.intro);
                        (Litex.complexAbs _wd_3_0 (by
                          let _atomic_wd_2_0 := _wd_3_0
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
                          (Litex.complexAbs _wd_3_0 (by
                            let _atomic_wd_3_0 := _wd_3_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact (by
                          let _litex_power := _atomic_wd_1_0
                          have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_1_0).val.base)
                          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInR _litex_power _recorded_power_base
                        )))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_71))
                    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_71))
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_71))
                    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))).val.function (by rfl) (by rfl)))) (And.intro (show (by
                    let _equal_wd_1_0 := (let _wd_1_0 := (Litex.euclideanNorm _value_i2 _value_i1 h_71 (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                      exact h_72));
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                      let _atomic_wd_1_0 := (Litex.euclideanNorm _value_i2 _value_i1 h_71 (by
                        let _atomic_wd_2_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                        exact h_72))
                      exact (Litex.euclideanNormInR _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                    let _equal_wd_1_1 := (Litex.finiteInnerProduct _value_i2 _value_i2 _value_i1 h_71 (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                      exact h_72) (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                      exact h_72))
                    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) from Litex.euclideanNormSquareInner (Litex.euclideanNorm _value_i2 _value_i1 h_71 (by
                    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                    exact h_72))) (show (by
                    let _atomic_wd_1_1 := (Litex.euclideanNorm _value_i2 _value_i1 h_71 (by
                      let _atomic_wd_2_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                      exact h_72))
                    exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) from Litex.euclideanNormNonnegative (Litex.euclideanNorm _value_i2 _value_i1 h_71 (by
                    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                    exact h_72))))))
                  )
                )
            )

          have h_74 : Litex.Same (let _wd_1_0 := (Litex.euclideanNorm _value_i2 _value_i1 h_61 (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
            exact h_69));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := (Litex.euclideanNorm _value_i2 _value_i1 h_61 (by
              let _atomic_wd_2_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
              exact h_69))
            exact (Litex.euclideanNormInR _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (Litex.finiteInnerProduct _value_i2 _value_i2 _value_i1 h_61 (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
            exact h_69) (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
            exact h_69)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_71 : Litex.In _value_i1 (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_61
                          )
                      )
                    have h_80 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.naturalNonnegative _value_i1 h_71)
                          )
                      )
                    have h_72 : (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                      exact Litex.In _value_i2 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                              exact h_69)
                          )
                      )
                    let _object_h89 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)))
                    have h_89 : Litex.In _value_i2 _object_h89 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inOfSame _value_i2 _value_i2 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61) _object_h89 (Litex.sameRefl _value_i2) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)) h_72)
                          )
                      )
                    exact (And.left (And.right (And.intro (show (by
                    let _equal_wd_1_0 := (let _wd_1_0 := (Litex.euclideanNorm _value_i2 _value_i1 h_71 (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                      exact h_72));
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                      let _atomic_wd_1_0 := (Litex.euclideanNorm _value_i2 _value_i1 h_71 (by
                        let _atomic_wd_2_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                        exact h_72))
                      exact (Litex.euclideanNormInR _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                    let _equal_wd_1_1 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_71));
                    let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i6)) (M.number (2 : ℂ)))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_1_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i6)) (M.number (2 : ℂ)))) _raw_i6) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i6 h_496 _
                        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_496)
                        have h_496 : Litex.In _value_i6 _wd_1_0 := h_496
                        have h_497 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_496).1
                              )
                          )
                        have h_498 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_496).2.1
                              )
                          )
                        have h_499 : Litex.Le _value_i6 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_496).2.2
                              )
                          )
                        have h_500 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_1_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_496)
                              )
                          )
                        change (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i6;
                          Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_89 (by
                            let _atomic_wd_2_1 := _wd_1_0
                            exact h_496) True.intro);
                          (Litex.complexAbs _wd_3_0 (by
                            let _atomic_wd_2_0 := _wd_3_0
                            exact (by
                              let _litex_return_call := _atomic_wd_2_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                            let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
                            (Litex.complexAbs _wd_3_0 (by
                              let _atomic_wd_3_0 := _wd_3_0
                              exact (by
                                let _litex_return_call := _atomic_wd_3_0
                                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                            exact (Litex.complexAbsInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                          exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i6;
                          Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_89 (by
                            let _atomic_wd_2_1 := _wd_1_0
                            exact h_496) True.intro);
                          (Litex.complexAbs _wd_3_0 (by
                            let _atomic_wd_2_0 := _wd_3_0
                            exact (by
                              let _litex_return_call := _atomic_wd_2_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                            let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
                            (Litex.complexAbs _wd_3_0 (by
                              let _atomic_wd_3_0 := _wd_3_0
                              exact (by
                                let _litex_return_call := _atomic_wd_3_0
                                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                            exact (Litex.complexAbsInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                          exact (by
                            let _litex_power := _atomic_wd_1_0
                            have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_1_0).val.base)
                            have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                            exact Litex.powStructuralInR _litex_power _recorded_power_base
                          )))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_71))
                      exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_71))
                      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_71))
                      exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) from (Litex.euclideanNormSquare (Litex.euclideanNorm _value_i2 _value_i1 h_71 (by
                    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                    exact h_72))).trans (congrArg M.number (Litex.euclideanNormSumFormula (Litex.euclideanNorm _value_i2 _value_i1 h_71 (by
                    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                    exact h_72)) ((let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_71));
                  let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i6)) (M.number (2 : ℂ)))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_1_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i6)) (M.number (2 : ℂ)))) _raw_i6) (Litex.denote (Litex.R (M := M))) := (by
                      intro _raw_i6 h_496 _
                      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_496)
                      have h_496 : Litex.In _value_i6 _wd_1_0 := h_496
                      have h_497 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_496).1
                            )
                        )
                      have h_498 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_496).2.1
                            )
                        )
                      have h_499 : Litex.Le _value_i6 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_496).2.2
                            )
                        )
                      have h_500 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_1_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_496)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i6;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_89 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_496) True.intro);
                        (Litex.complexAbs _wd_3_0 (by
                          let _atomic_wd_2_0 := _wd_3_0
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
                          (Litex.complexAbs _wd_3_0 (by
                            let _atomic_wd_3_0 := _wd_3_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i6;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_89 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_496) True.intro);
                        (Litex.complexAbs _wd_3_0 (by
                          let _atomic_wd_2_0 := _wd_3_0
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
                          (Litex.complexAbs _wd_3_0 (by
                            let _atomic_wd_3_0 := _wd_3_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact (by
                          let _litex_power := _atomic_wd_1_0
                          have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_1_0).val.base)
                          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInR _litex_power _recorded_power_base
                        )))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_71))
                    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_71))
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_71))
                    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))).val.function (by rfl) (by rfl)))) (And.intro (show (by
                    let _equal_wd_1_0 := (let _wd_1_0 := (Litex.euclideanNorm _value_i2 _value_i1 h_71 (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                      exact h_72));
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                      let _atomic_wd_1_0 := (Litex.euclideanNorm _value_i2 _value_i1 h_71 (by
                        let _atomic_wd_2_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                        exact h_72))
                      exact (Litex.euclideanNormInR _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                    let _equal_wd_1_1 := (Litex.finiteInnerProduct _value_i2 _value_i2 _value_i1 h_71 (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                      exact h_72) (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                      exact h_72))
                    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) from Litex.euclideanNormSquareInner (Litex.euclideanNorm _value_i2 _value_i1 h_71 (by
                    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                    exact h_72))) (show (by
                    let _atomic_wd_1_1 := (Litex.euclideanNorm _value_i2 _value_i1 h_71 (by
                      let _atomic_wd_2_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                      exact h_72))
                    exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) from Litex.euclideanNormNonnegative (Litex.euclideanNorm _value_i2 _value_i1 h_71 (by
                    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                    exact h_72)))))))
                  )
                )
            )

          have h_75 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.euclideanNorm _value_i2 _value_i1 h_61 (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
            exact h_69)) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    have h_71 : Litex.In _value_i1 (Litex.N (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            h_61
                          )
                      )
                    have h_80 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.naturalNonnegative _value_i1 h_71)
                          )
                      )
                    have h_72 : (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                      exact Litex.In _value_i2 _atomic_wd_1_1) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (by
                              let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                              exact h_69)
                          )
                      )
                    let _object_h89 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)))
                    have h_89 : Litex.In _value_i2 _object_h89 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inOfSame _value_i2 _value_i2 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61) _object_h89 (Litex.sameRefl _value_i2) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)) h_72)
                          )
                      )
                    exact (And.right (And.right (And.intro (show (by
                    let _equal_wd_1_0 := (let _wd_1_0 := (Litex.euclideanNorm _value_i2 _value_i1 h_71 (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                      exact h_72));
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                      let _atomic_wd_1_0 := (Litex.euclideanNorm _value_i2 _value_i1 h_71 (by
                        let _atomic_wd_2_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                        exact h_72))
                      exact (Litex.euclideanNormInR _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                    let _equal_wd_1_1 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_71));
                    let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i6)) (M.number (2 : ℂ)))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_1_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i6)) (M.number (2 : ℂ)))) _raw_i6) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i6 h_496 _
                        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_496)
                        have h_496 : Litex.In _value_i6 _wd_1_0 := h_496
                        have h_497 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_496).1
                              )
                          )
                        have h_498 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_496).2.1
                              )
                          )
                        have h_499 : Litex.Le _value_i6 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_496).2.2
                              )
                          )
                        have h_500 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_1_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_496)
                              )
                          )
                        change (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i6;
                          Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_89 (by
                            let _atomic_wd_2_1 := _wd_1_0
                            exact h_496) True.intro);
                          (Litex.complexAbs _wd_3_0 (by
                            let _atomic_wd_2_0 := _wd_3_0
                            exact (by
                              let _litex_return_call := _atomic_wd_2_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                            let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
                            (Litex.complexAbs _wd_3_0 (by
                              let _atomic_wd_3_0 := _wd_3_0
                              exact (by
                                let _litex_return_call := _atomic_wd_3_0
                                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                            exact (Litex.complexAbsInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                          exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i6;
                          Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_89 (by
                            let _atomic_wd_2_1 := _wd_1_0
                            exact h_496) True.intro);
                          (Litex.complexAbs _wd_3_0 (by
                            let _atomic_wd_2_0 := _wd_3_0
                            exact (by
                              let _litex_return_call := _atomic_wd_2_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                            let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
                            (Litex.complexAbs _wd_3_0 (by
                              let _atomic_wd_3_0 := _wd_3_0
                              exact (by
                                let _litex_return_call := _atomic_wd_3_0
                                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                            exact (Litex.complexAbsInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                          exact (by
                            let _litex_power := _atomic_wd_1_0
                            have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_1_0).val.base)
                            have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                            exact Litex.powStructuralInR _litex_power _recorded_power_base
                          )))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_71))
                      exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_71))
                      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_71))
                      exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) from (Litex.euclideanNormSquare (Litex.euclideanNorm _value_i2 _value_i1 h_71 (by
                    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                    exact h_72))).trans (congrArg M.number (Litex.euclideanNormSumFormula (Litex.euclideanNorm _value_i2 _value_i1 h_71 (by
                    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                    exact h_72)) ((let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_71));
                  let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i6)) (M.number (2 : ℂ)))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_1_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i6)) (M.number (2 : ℂ)))) _raw_i6) (Litex.denote (Litex.R (M := M))) := (by
                      intro _raw_i6 h_496 _
                      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_496)
                      have h_496 : Litex.In _value_i6 _wd_1_0 := h_496
                      have h_497 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_496).1
                            )
                        )
                      have h_498 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_496).2.1
                            )
                        )
                      have h_499 : Litex.Le _value_i6 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_1_0 _value_i6 h_496).2.2
                            )
                        )
                      have h_500 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_1_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_496)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i6;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_89 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_496) True.intro);
                        (Litex.complexAbs _wd_3_0 (by
                          let _atomic_wd_2_0 := _wd_3_0
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
                          (Litex.complexAbs _wd_3_0 (by
                            let _atomic_wd_3_0 := _wd_3_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i6;
                        Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_89 (by
                          let _atomic_wd_2_1 := _wd_1_0
                          exact h_496) True.intro);
                        (Litex.complexAbs _wd_3_0 (by
                          let _atomic_wd_2_0 := _wd_3_0
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
                          (Litex.complexAbs _wd_3_0 (by
                            let _atomic_wd_3_0 := _wd_3_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact (by
                          let _litex_power := _atomic_wd_1_0
                          have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_1_0).val.base)
                          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInR _litex_power _recorded_power_base
                        )))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_71))
                    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_71))
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_71))
                    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))).val.function (by rfl) (by rfl)))) (And.intro (show (by
                    let _equal_wd_1_0 := (let _wd_1_0 := (Litex.euclideanNorm _value_i2 _value_i1 h_71 (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                      exact h_72));
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.powNatReal _wd_1_0 _wd_1_1 (2 : ℕ) (by
                      let _atomic_wd_1_0 := (Litex.euclideanNorm _value_i2 _value_i1 h_71 (by
                        let _atomic_wd_2_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                        exact h_72))
                      exact (Litex.euclideanNormInR _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_1_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                    let _equal_wd_1_1 := (Litex.finiteInnerProduct _value_i2 _value_i2 _value_i1 h_71 (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                      exact h_72) (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                      exact h_72))
                    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) from Litex.euclideanNormSquareInner (Litex.euclideanNorm _value_i2 _value_i1 h_71 (by
                    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                    exact h_72))) (show (by
                    let _atomic_wd_1_1 := (Litex.euclideanNorm _value_i2 _value_i1 h_71 (by
                      let _atomic_wd_2_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                      exact h_72))
                    exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) from Litex.euclideanNormNonnegative (Litex.euclideanNorm _value_i2 _value_i1 h_71 (by
                    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                    exact h_72)))))))
                  )
                )
            )
          have h_3 : (by
            let _atomic_wd_1_1 := (Litex.euclideanNorm _value_i2 _value_i1 h_61 (by
              let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
              exact h_69))
            exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (Litex.euclideanNorm _value_i2 _value_i1 h_61 (by
                      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
                      exact h_69))
                    exact h_75)
                )
            )
          exact (by
            let _atomic_wd_1_1 := (Litex.euclideanNorm _value_i2 _value_i1 h_61 (by
              let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_61)
              exact h_69))
            exact h_75)
        )
      )
  )

theorem h_4414 : (by
  have h_4415 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.N (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
        )
    )
  have h_4416 : (by
    let _atomic_wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) Complex.I)] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) Complex.I)) (fun i => Fin.elim0 i))))
    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_4415)
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) Complex.I)] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) Complex.I)) (fun i => Fin.elim0 i))))
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_4415)
            exact (by
              let _membership_function := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) Complex.I)] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) Complex.I)) (fun i => Fin.elim0 i))))
              let _membership_target := (let _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → True := (by
                  intro _raw_i10 h_4437 _
                  let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_4437)
                  have h_4437 : Litex.In _value_i10 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) := h_4437
                  have h_4438 : Litex.In _value_i10 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i10 h_4437).1
                        )
                    )
                  have h_4439 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i10 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i10 h_4437).2.1
                        )
                    )
                  have h_4440 : Litex.Le _value_i10 (Litex.number (M := M) (2 : ℂ)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i10 h_4437).2.2
                        )
                    )
                  have h_4441 : Litex.In _value_i10 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i10 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_4437)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)))
              have h_4442 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.C (M := M)) := (Litex.numberInC (M := M) (1 : ℂ))
              have h_4443 : Litex.In (Litex.number (M := M) Complex.I) (Litex.C (M := M)) := (Litex.numberInC (M := M) Complex.I)
              exact (by
                let _source_cart := (Litex.tupleSingletonCart _atomic_wd_1_0)
                have _source_member : Litex.In _membership_function _source_cart := (by
                let _tuple := _atomic_wd_1_0
                let _receiver := _atomic_wd_1_0
                have _same : Litex.Same _receiver _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
                have _domain : _membership_target.val.domain = Litex.FiniteFunction.indexSet (M := M) 2 := by
                  change Litex.finiteSeqDomain (Litex.number (M := M) (2 : ℂ)) = _
                  exact Litex.finiteSeqDomain_ofDenote (M := M) (Litex.number (M := M) (2 : ℂ)) 2 (by change M.number (2 : ℂ) = M.number ((2 : ℕ) : ℂ); norm_num)
                apply Litex.cartMemberInFnSetOfReturns _membership_function _source_cart _membership_target.val _source_member _domain
                let _tuple := _atomic_wd_1_0
                have _same : Litex.Same _membership_function _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                have _values : ∀ i : Fin 2, M.mem (_tuple.val.values i) _membership_target.val.output := (by
                have _finiteProof_0 := (h_4442)
                have _finiteProof_1 := (h_4443)
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )
                intro _input _hin
                rw [_domain] at _hin
                obtain ⟨_index, rfl⟩ := (Litex.FiniteFunction.indexSet_members (M := M) (n := 2) _input).mp _hin
                have _coordinate := (congrArg (fun p => Litex.FunctionSemantics.callValue (M := M) p (Litex.FiniteFunction.index _index)) _same).trans (Litex.tuple_coordinate _tuple _index)
                change M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) _) _membership_target.val.output
                rw [_coordinate]
                exact _values _index)))
        )
    )
  exact (by
    let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) Complex.I)] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) Complex.I)) (fun i => Fin.elim0 i))));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.euclideanNorm _wd_1_0 _wd_1_1 h_4415 (by
      let _atomic_wd_1_0 := _wd_1_0
      let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_4415)
      exact h_4416)))
    exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_4415 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.N (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))
                )
            )
          have h_4418 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative (Litex.number (M := M) (2 : ℂ)) h_4415)
                )
            )
          have h_4416 : (by
            let _atomic_wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) Complex.I)] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) Complex.I)) (fun i => Fin.elim0 i))))
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_4415)
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) Complex.I)] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) Complex.I)) (fun i => Fin.elim0 i))))
                    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_4415)
                    exact (by
                      let _membership_function := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) Complex.I)] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) Complex.I)) (fun i => Fin.elim0 i))))
                      let _membership_target := (let _checked_header : ∀ (_raw_i10 : M.Value), M.mem _raw_i10 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) → ((fun (_raw_i10 : M.Value) => True) _raw_i10) → True := (by
                          intro _raw_i10 h_4437 _
                          let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_4437)
                          have h_4437 : Litex.In _value_i10 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) := h_4437
                          have h_4438 : Litex.In _value_i10 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i10 h_4437).1
                                )
                            )
                          have h_4439 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i10 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i10 h_4437).2.1
                                )
                            )
                          have h_4440 : Litex.Le _value_i10 (Litex.number (M := M) (2 : ℂ)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i10 h_4437).2.2
                                )
                            )
                          have h_4441 : Litex.In _value_i10 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i10 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_4437)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i10 : M.Value) => True) _litex_input)))
                      have h_4442 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.C (M := M)) := (Litex.numberInC (M := M) (1 : ℂ))
                      have h_4443 : Litex.In (Litex.number (M := M) Complex.I) (Litex.C (M := M)) := (Litex.numberInC (M := M) Complex.I)
                      exact (by
                        let _source_cart := (Litex.tupleSingletonCart _atomic_wd_1_0)
                        have _source_member : Litex.In _membership_function _source_cart := (by
                        let _tuple := _atomic_wd_1_0
                        let _receiver := _atomic_wd_1_0
                        have _same : Litex.Same _receiver _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                        exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
                        have _domain : _membership_target.val.domain = Litex.FiniteFunction.indexSet (M := M) 2 := by
                          change Litex.finiteSeqDomain (Litex.number (M := M) (2 : ℂ)) = _
                          exact Litex.finiteSeqDomain_ofDenote (M := M) (Litex.number (M := M) (2 : ℂ)) 2 (by change M.number (2 : ℂ) = M.number ((2 : ℕ) : ℂ); norm_num)
                        apply Litex.cartMemberInFnSetOfReturns _membership_function _source_cart _membership_target.val _source_member _domain
                        let _tuple := _atomic_wd_1_0
                        have _same : Litex.Same _membership_function _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                        have _values : ∀ i : Fin 2, M.mem (_tuple.val.values i) _membership_target.val.output := (by
                        have _finiteProof_0 := (h_4442)
                        have _finiteProof_1 := (h_4443)
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )
                        intro _input _hin
                        rw [_domain] at _hin
                        obtain ⟨_index, rfl⟩ := (Litex.FiniteFunction.indexSet_members (M := M) (n := 2) _input).mp _hin
                        have _coordinate := (congrArg (fun p => Litex.FunctionSemantics.callValue (M := M) p (Litex.FiniteFunction.index _index)) _same).trans (Litex.tuple_coordinate _tuple _index)
                        change M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) _) _membership_target.val.output
                        rw [_coordinate]
                        exact _values _index)))
                )
            )
          let _object_h4448 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_4415)))
          have h_4448 : Litex.In (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) Complex.I)] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) Complex.I)) (fun i => Fin.elim0 i)))) _object_h4448 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) Complex.I)] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) Complex.I)) (fun i => Fin.elim0 i)))) (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) Complex.I)] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) Complex.I)) (fun i => Fin.elim0 i)))) (Litex.finiteSeq (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_4415) _object_h4448 (Litex.sameRefl (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) Complex.I)] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) Complex.I)) (fun i => Fin.elim0 i))))) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_4415)) h_4416)
                )
            )
          have h_4417 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) Complex.I)] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) Complex.I)) (fun i => Fin.elim0 i))));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.euclideanNorm _wd_1_0 _wd_1_1 h_4415 (by
            let _atomic_wd_1_0 := _wd_1_0
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_4415)
            exact h_4416))) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_2 (M := M)) (Litex.number (M := M) (2 : ℂ)) h_4415 (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) Complex.I)] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) Complex.I)) (fun i => Fin.elim0 i)))) h_4416)
                )
            )
          exact (by
          let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) Complex.I)] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) Complex.I)) (fun i => Fin.elim0 i))));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.euclideanNorm _wd_1_0 _wd_1_1 h_4415 (by
            let _atomic_wd_1_0 := _wd_1_0
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) h_4415)
            exact h_4416)))
          exact h_4417)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_euclidean_x5f_norm_x5f_nonnegative_x2f_statement_x2e_lit
