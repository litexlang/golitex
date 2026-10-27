import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_euclidean_x5f_norm_x5f_definition_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_19 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_27 : Litex.In _value_i2 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_19)) (h_1 : (by
  let _object_h28 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_19)))
  have h_28 : Litex.In _value_i2 _object_h28 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i2 _value_i2 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_19) _object_h28 (Litex.sameRefl _value_i2) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_19)) h_27)
        )
    )
  exact (by
    let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
    let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i3)) (M.number (2 : ℂ)))) _litex_input) (by
      have _litex_checked_return : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (Litex.denote _wd_1_0) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → M.mem ((fun (_raw_i3 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i3)) (M.number (2 : ℂ)))) _raw_i3) (Litex.denote (Litex.R (M := M))) := (by
        intro _raw_i3 h_227 _
        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_227)
        have h_227 : Litex.In _value_i3 _wd_1_0 := h_227
        have h_228 : Litex.In _value_i3 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_227).1
              )
          )
        have h_229 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i3 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_227).2.1
              )
          )
        have h_230 : Litex.Le _value_i3 _value_i1 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_227).2.2
              )
          )
        have h_231 : Litex.In _value_i3 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive _wd_1_0 _value_i3 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_227)
              )
          )
        change (by
          let _atomic_wd_2_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i3;
          Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
            let _atomic_wd_3_1 := _wd_1_0
            exact h_227) True.intro);
          (Litex.complexAbs _wd_3_0 (by
            let _atomic_wd_3_0 := _wd_3_0
            exact (by
              let _litex_return_call := _atomic_wd_3_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_3_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
            (Litex.complexAbs _wd_3_0 (by
              let _atomic_wd_4_0 := _wd_3_0
              exact (by
                let _litex_return_call := _atomic_wd_4_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
            exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
        exact (by
          let _atomic_wd_2_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i3;
          Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
            let _atomic_wd_3_1 := _wd_1_0
            exact h_227) True.intro);
          (Litex.complexAbs _wd_3_0 (by
            let _atomic_wd_3_0 := _wd_3_0
            exact (by
              let _litex_return_call := _atomic_wd_3_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_3_0 := (let _wd_3_0 := (_wd_2_0).val.arg;
            (Litex.complexAbs _wd_3_0 (by
              let _atomic_wd_4_0 := _wd_3_0
              exact (by
                let _litex_return_call := _atomic_wd_4_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
            exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
          exact (by
            let _litex_power := _atomic_wd_2_0
            have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
            have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
            exact Litex.powStructuralInR _litex_power _recorded_power_base
          )))
      intro _litex_input _litex_domain
      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
      exact _litex_checked_return _litex_input _litex_members _litex_guard));
    (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (by
      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
      exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
      exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
    exact Litex.Le (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1)
)), (by
  let _object_h28 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_19)))
  have h_28 : Litex.In _value_i2 _object_h28 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i2 _value_i2 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_19) _object_h28 (Litex.sameRefl _value_i2) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_19)) h_27)
        )
    )
  let _object_w50 := (Litex.euclideanNorm _value_i2 _value_i1 h_19 (by
    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_19)
    exact h_27))
  let _object_w51 := (let _wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
  let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i4)) (M.number (2 : ℂ)))) _litex_input) (by
    have _litex_checked_return : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _wd_2_0) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → M.mem ((fun (_raw_i4 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i4)) (M.number (2 : ℂ)))) _raw_i4) (Litex.denote (Litex.R (M := M))) := (by
      intro _raw_i4 h_2335 _
      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_2335)
      have h_2335 : Litex.In _value_i4 _wd_2_0 := h_2335
      have h_2336 : Litex.In _value_i4 (Litex.Z (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds _wd_2_0 _value_i4 h_2335).1
            )
        )
      have h_2337 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds _wd_2_0 _value_i4 h_2335).2.1
            )
        )
      have h_2338 : Litex.Le _value_i4 _value_i1 :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangeBounds _wd_2_0 _value_i4 h_2335).2.2
            )
        )
      have h_2339 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
        (by
          litex_checked_step =>
            exact (
              (Litex.inClosedRangePositive _wd_2_0 _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2335)
            )
        )
      change (by
        let _atomic_wd_1_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
        Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
          let _atomic_wd_2_1 := _wd_2_0
          exact h_2335) True.intro);
        (Litex.complexAbs _wd_4_0 (by
          let _atomic_wd_2_0 := _wd_4_0
          exact (by
            let _litex_return_call := _atomic_wd_2_0
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
        let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
          let _atomic_wd_2_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
          (Litex.complexAbs _wd_4_0 (by
            let _atomic_wd_3_0 := _wd_4_0
            exact (by
              let _litex_return_call := _atomic_wd_3_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
          exact (Litex.complexAbsInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
      exact (by
        let _atomic_wd_1_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
        Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
          let _atomic_wd_2_1 := _wd_2_0
          exact h_2335) True.intro);
        (Litex.complexAbs _wd_4_0 (by
          let _atomic_wd_2_0 := _wd_4_0
          exact (by
            let _litex_return_call := _atomic_wd_2_0
            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
        let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
          let _atomic_wd_2_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
          (Litex.complexAbs _wd_4_0 (by
            let _atomic_wd_3_0 := _wd_4_0
            exact (by
              let _litex_return_call := _atomic_wd_3_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
          exact (Litex.complexAbsInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
        exact (by
          let _litex_power := _atomic_wd_1_0
          have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_1_0).val.base)
          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
          exact Litex.powStructuralInR _litex_power _recorded_power_base
        )))
    intro _litex_input _litex_domain
    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
    exact _litex_checked_return _litex_input _litex_members _litex_guard));
  (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (by
    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)));
  (Litex.sqrt _wd_1_0 (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
    let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i4)) (M.number (2 : ℂ)))) _litex_input) (by
      have _litex_checked_return : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _wd_2_0) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → M.mem ((fun (_raw_i4 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i4)) (M.number (2 : ℂ)))) _raw_i4) (Litex.denote (Litex.R (M := M))) := (by
        intro _raw_i4 h_3328 _
        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_3328)
        have h_3328 : Litex.In _value_i4 _wd_2_0 := h_3328
        have h_3329 : Litex.In _value_i4 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_2_0 _value_i4 h_3328).1
              )
          )
        have h_3330 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_2_0 _value_i4 h_3328).2.1
              )
          )
        have h_3331 : Litex.Le _value_i4 _value_i1 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_2_0 _value_i4 h_3328).2.2
              )
          )
        have h_3332 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive _wd_2_0 _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3328)
              )
          )
        change (by
          let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
          Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
            let _atomic_wd_3_1 := _wd_2_0
            exact h_3328) True.intro);
          (Litex.complexAbs _wd_4_0 (by
            let _atomic_wd_3_0 := _wd_4_0
            exact (by
              let _litex_return_call := _atomic_wd_3_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
          let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
            let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
            (Litex.complexAbs _wd_4_0 (by
              let _atomic_wd_4_0 := _wd_4_0
              exact (by
                let _litex_return_call := _atomic_wd_4_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
            exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
        exact (by
          let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
          Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
            let _atomic_wd_3_1 := _wd_2_0
            exact h_3328) True.intro);
          (Litex.complexAbs _wd_4_0 (by
            let _atomic_wd_3_0 := _wd_4_0
            exact (by
              let _litex_return_call := _atomic_wd_3_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
          let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
            let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
            (Litex.complexAbs _wd_4_0 (by
              let _atomic_wd_4_0 := _wd_4_0
              exact (by
                let _litex_return_call := _atomic_wd_4_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
            exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
          exact (by
            let _litex_power := _atomic_wd_2_0
            have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
            have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
            exact Litex.powStructuralInR _litex_power _recorded_power_base
          )))
      intro _litex_input _litex_domain
      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
      exact _litex_checked_return _litex_input _litex_members _litex_guard));
    (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (by
      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
      exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
      exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
    exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)) (by
    let _atomic_wd_1_1 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
    let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i4)) (M.number (2 : ℂ)))) _litex_input) (by
      have _litex_checked_return : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _wd_2_0) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → M.mem ((fun (_raw_i4 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i4)) (M.number (2 : ℂ)))) _raw_i4) (Litex.denote (Litex.R (M := M))) := (by
        intro _raw_i4 h_4388 _
        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_4388)
        have h_4388 : Litex.In _value_i4 _wd_2_0 := h_4388
        have h_4389 : Litex.In _value_i4 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_2_0 _value_i4 h_4388).1
              )
          )
        have h_4390 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_2_0 _value_i4 h_4388).2.1
              )
          )
        have h_4391 : Litex.Le _value_i4 _value_i1 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_2_0 _value_i4 h_4388).2.2
              )
          )
        have h_4392 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive _wd_2_0 _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_4388)
              )
          )
        change (by
          let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
          Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
            let _atomic_wd_3_1 := _wd_2_0
            exact h_4388) True.intro);
          (Litex.complexAbs _wd_4_0 (by
            let _atomic_wd_3_0 := _wd_4_0
            exact (by
              let _litex_return_call := _atomic_wd_3_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
          let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
            let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
            (Litex.complexAbs _wd_4_0 (by
              let _atomic_wd_4_0 := _wd_4_0
              exact (by
                let _litex_return_call := _atomic_wd_4_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
            exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
        exact (by
          let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
          Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
            let _atomic_wd_3_1 := _wd_2_0
            exact h_4388) True.intro);
          (Litex.complexAbs _wd_4_0 (by
            let _atomic_wd_3_0 := _wd_4_0
            exact (by
              let _litex_return_call := _atomic_wd_3_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
          let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
            let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
            (Litex.complexAbs _wd_4_0 (by
              let _atomic_wd_4_0 := _wd_4_0
              exact (by
                let _litex_return_call := _atomic_wd_4_0
                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
            exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
          exact (by
            let _litex_power := _atomic_wd_2_0
            have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
            have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
            exact Litex.powStructuralInR _litex_power _recorded_power_base
          )))
      intro _litex_input _litex_domain
      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
      exact _litex_checked_return _litex_input _litex_members _litex_guard));
    (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (by
      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
      exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
      exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
    exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
    let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i3)) (M.number (2 : ℂ)))) _litex_input) (by
      have _litex_checked_return : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (Litex.denote _wd_1_0) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → M.mem ((fun (_raw_i3 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i3)) (M.number (2 : ℂ)))) _raw_i3) (Litex.denote (Litex.R (M := M))) := (by
        intro _raw_i3 h_1227 _
        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1227)
        have h_1227 : Litex.In _value_i3 _wd_1_0 := h_1227
        have h_1228 : Litex.In _value_i3 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).1
              )
          )
        have h_1229 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i3 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).2.1
              )
          )
        have h_1230 : Litex.Le _value_i3 _value_i1 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).2.2
              )
          )
        have h_1231 : Litex.In _value_i3 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive _wd_1_0 _value_i3 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1227)
              )
          )
        change (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i3;
          Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
            let _atomic_wd_2_1 := _wd_1_0
            exact h_1227) True.intro);
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
          let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i3;
          Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
            let _atomic_wd_2_1 := _wd_1_0
            exact h_1227) True.intro);
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
      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
      exact _litex_checked_return _litex_input _litex_members _litex_guard));
    (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (by
      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
      exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
      exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
      let _left := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
    let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i3)) (M.number (2 : ℂ)))) _litex_input) (by
      have _litex_checked_return : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (Litex.denote _wd_1_0) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → M.mem ((fun (_raw_i3 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i3)) (M.number (2 : ℂ)))) _raw_i3) (Litex.denote (Litex.R (M := M))) := (by
        intro _raw_i3 h_1227 _
        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1227)
        have h_1227 : Litex.In _value_i3 _wd_1_0 := h_1227
        have h_1228 : Litex.In _value_i3 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).1
              )
          )
        have h_1229 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i3 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).2.1
              )
          )
        have h_1230 : Litex.Le _value_i3 _value_i1 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).2.2
              )
          )
        have h_1231 : Litex.In _value_i3 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive _wd_1_0 _value_i3 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1227)
              )
          )
        change (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i3;
          Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
            let _atomic_wd_2_1 := _wd_1_0
            exact h_1227) True.intro);
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
          let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i3;
          Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
            let _atomic_wd_2_1 := _wd_1_0
            exact h_1227) True.intro);
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
      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
      exact _litex_checked_return _litex_input _litex_members _litex_guard));
    (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (by
      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
      exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
      exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
      let _right := _atomic_wd_1_1
      exact (show Litex.Same _left _right from rfl)) h_1))))
  exact (by
    let _equal_wd_1_0 := _object_w50
    let _equal_wd_1_1 := _object_w51
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_19 _Host_i2 _rep_i2 _value_i2 h_27 h_1
          have h_20 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_19)
                )
            )
          let _object_h28 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_19)))
          have h_28 : Litex.In _value_i2 _object_h28 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i2 _value_i2 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_19) _object_h28 (Litex.sameRefl _value_i2) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_19)) h_27)
                )
            )
          let _object_w50 := (Litex.euclideanNorm _value_i2 _value_i1 h_19 (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_19)
            exact h_27))
          let _object_w51 := (let _wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
          let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i4)) (M.number (2 : ℂ)))) _litex_input) (by
            have _litex_checked_return : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _wd_2_0) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → M.mem ((fun (_raw_i4 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i4)) (M.number (2 : ℂ)))) _raw_i4) (Litex.denote (Litex.R (M := M))) := (by
              intro _raw_i4 h_2335 _
              let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_2335)
              have h_2335 : Litex.In _value_i4 _wd_2_0 := h_2335
              have h_2336 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_2_0 _value_i4 h_2335).1
                    )
                )
              have h_2337 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_2_0 _value_i4 h_2335).2.1
                    )
                )
              have h_2338 : Litex.Le _value_i4 _value_i1 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangeBounds _wd_2_0 _value_i4 h_2335).2.2
                    )
                )
              have h_2339 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inClosedRangePositive _wd_2_0 _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_2335)
                    )
                )
              change (by
                let _atomic_wd_1_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                  let _atomic_wd_2_1 := _wd_2_0
                  exact h_2335) True.intro);
                (Litex.complexAbs _wd_4_0 (by
                  let _atomic_wd_2_0 := _wd_4_0
                  exact (by
                    let _litex_return_call := _atomic_wd_2_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                  let _atomic_wd_2_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                  (Litex.complexAbs _wd_4_0 (by
                    let _atomic_wd_3_0 := _wd_4_0
                    exact (by
                      let _litex_return_call := _atomic_wd_3_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                  exact (Litex.complexAbsInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
              exact (by
                let _atomic_wd_1_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                  let _atomic_wd_2_1 := _wd_2_0
                  exact h_2335) True.intro);
                (Litex.complexAbs _wd_4_0 (by
                  let _atomic_wd_2_0 := _wd_4_0
                  exact (by
                    let _litex_return_call := _atomic_wd_2_0
                    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                  let _atomic_wd_2_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                  (Litex.complexAbs _wd_4_0 (by
                    let _atomic_wd_3_0 := _wd_4_0
                    exact (by
                      let _litex_return_call := _atomic_wd_3_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                  exact (Litex.complexAbsInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                exact (by
                  let _litex_power := _atomic_wd_1_0
                  have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_1_0).val.base)
                  have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                  have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                  have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                  exact Litex.powStructuralInR _litex_power _recorded_power_base
                )))
            intro _litex_input _litex_domain
            obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
            exact _litex_checked_return _litex_input _litex_members _litex_guard));
          (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (by
            let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
            exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
            let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
            exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)));
          (Litex.sqrt _wd_1_0 (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
            let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i4)) (M.number (2 : ℂ)))) _litex_input) (by
              have _litex_checked_return : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _wd_2_0) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → M.mem ((fun (_raw_i4 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i4)) (M.number (2 : ℂ)))) _raw_i4) (Litex.denote (Litex.R (M := M))) := (by
                intro _raw_i4 h_3328 _
                let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_3328)
                have h_3328 : Litex.In _value_i4 _wd_2_0 := h_3328
                have h_3329 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds _wd_2_0 _value_i4 h_3328).1
                      )
                  )
                have h_3330 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds _wd_2_0 _value_i4 h_3328).2.1
                      )
                  )
                have h_3331 : Litex.Le _value_i4 _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds _wd_2_0 _value_i4 h_3328).2.2
                      )
                  )
                have h_3332 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive _wd_2_0 _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_3328)
                      )
                  )
                change (by
                  let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                  Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                    let _atomic_wd_3_1 := _wd_2_0
                    exact h_3328) True.intro);
                  (Litex.complexAbs _wd_4_0 (by
                    let _atomic_wd_3_0 := _wd_4_0
                    exact (by
                      let _litex_return_call := _atomic_wd_3_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                  let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                    let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                    (Litex.complexAbs _wd_4_0 (by
                      let _atomic_wd_4_0 := _wd_4_0
                      exact (by
                        let _litex_return_call := _atomic_wd_4_0
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                    exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                  exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                exact (by
                  let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                  Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                    let _atomic_wd_3_1 := _wd_2_0
                    exact h_3328) True.intro);
                  (Litex.complexAbs _wd_4_0 (by
                    let _atomic_wd_3_0 := _wd_4_0
                    exact (by
                      let _litex_return_call := _atomic_wd_3_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                  let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                    let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                    (Litex.complexAbs _wd_4_0 (by
                      let _atomic_wd_4_0 := _wd_4_0
                      exact (by
                        let _litex_return_call := _atomic_wd_4_0
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                    exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                  exact (by
                    let _litex_power := _atomic_wd_2_0
                    have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                    have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                    have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                    have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                    exact Litex.powStructuralInR _litex_power _recorded_power_base
                  )))
              intro _litex_input _litex_domain
              obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
              exact _litex_checked_return _litex_input _litex_members _litex_guard));
            (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (by
              let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
              exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
              let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
              let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
              exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
            exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)) (by
            let _atomic_wd_1_1 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
            let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i4)) (M.number (2 : ℂ)))) _litex_input) (by
              have _litex_checked_return : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _wd_2_0) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → M.mem ((fun (_raw_i4 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i4)) (M.number (2 : ℂ)))) _raw_i4) (Litex.denote (Litex.R (M := M))) := (by
                intro _raw_i4 h_4388 _
                let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_4388)
                have h_4388 : Litex.In _value_i4 _wd_2_0 := h_4388
                have h_4389 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds _wd_2_0 _value_i4 h_4388).1
                      )
                  )
                have h_4390 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds _wd_2_0 _value_i4 h_4388).2.1
                      )
                  )
                have h_4391 : Litex.Le _value_i4 _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds _wd_2_0 _value_i4 h_4388).2.2
                      )
                  )
                have h_4392 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive _wd_2_0 _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_4388)
                      )
                  )
                change (by
                  let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                  Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                    let _atomic_wd_3_1 := _wd_2_0
                    exact h_4388) True.intro);
                  (Litex.complexAbs _wd_4_0 (by
                    let _atomic_wd_3_0 := _wd_4_0
                    exact (by
                      let _litex_return_call := _atomic_wd_3_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                  let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                    let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                    (Litex.complexAbs _wd_4_0 (by
                      let _atomic_wd_4_0 := _wd_4_0
                      exact (by
                        let _litex_return_call := _atomic_wd_4_0
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                    exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                  exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                exact (by
                  let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                  Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                    let _atomic_wd_3_1 := _wd_2_0
                    exact h_4388) True.intro);
                  (Litex.complexAbs _wd_4_0 (by
                    let _atomic_wd_3_0 := _wd_4_0
                    exact (by
                      let _litex_return_call := _atomic_wd_3_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                  let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                    let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                    (Litex.complexAbs _wd_4_0 (by
                      let _atomic_wd_4_0 := _wd_4_0
                      exact (by
                        let _litex_return_call := _atomic_wd_4_0
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                    exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                  exact (by
                    let _litex_power := _atomic_wd_2_0
                    have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                    have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                    have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                    have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                    exact Litex.powStructuralInR _litex_power _recorded_power_base
                  )))
              intro _litex_input _litex_domain
              obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
              exact _litex_checked_return _litex_input _litex_members _litex_guard));
            (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (by
              let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
              exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
              let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
              let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
              exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
            exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
            let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i3)) (M.number (2 : ℂ)))) _litex_input) (by
              have _litex_checked_return : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (Litex.denote _wd_1_0) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → M.mem ((fun (_raw_i3 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i3)) (M.number (2 : ℂ)))) _raw_i3) (Litex.denote (Litex.R (M := M))) := (by
                intro _raw_i3 h_1227 _
                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1227)
                have h_1227 : Litex.In _value_i3 _wd_1_0 := h_1227
                have h_1228 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).1
                      )
                  )
                have h_1229 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i3 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).2.1
                      )
                  )
                have h_1230 : Litex.Le _value_i3 _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).2.2
                      )
                  )
                have h_1231 : Litex.In _value_i3 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive _wd_1_0 _value_i3 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1227)
                      )
                  )
                change (by
                  let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i3;
                  Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                    let _atomic_wd_2_1 := _wd_1_0
                    exact h_1227) True.intro);
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
                  let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i3;
                  Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                    let _atomic_wd_2_1 := _wd_1_0
                    exact h_1227) True.intro);
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
              obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
              exact _litex_checked_return _litex_input _litex_members _litex_guard));
            (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (by
              let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
              exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
              let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
              let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
              exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
              let _left := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
            let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i3)) (M.number (2 : ℂ)))) _litex_input) (by
              have _litex_checked_return : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (Litex.denote _wd_1_0) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → M.mem ((fun (_raw_i3 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i3)) (M.number (2 : ℂ)))) _raw_i3) (Litex.denote (Litex.R (M := M))) := (by
                intro _raw_i3 h_1227 _
                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1227)
                have h_1227 : Litex.In _value_i3 _wd_1_0 := h_1227
                have h_1228 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).1
                      )
                  )
                have h_1229 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i3 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).2.1
                      )
                  )
                have h_1230 : Litex.Le _value_i3 _value_i1 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).2.2
                      )
                  )
                have h_1231 : Litex.In _value_i3 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive _wd_1_0 _value_i3 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1227)
                      )
                  )
                change (by
                  let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i3;
                  Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                    let _atomic_wd_2_1 := _wd_1_0
                    exact h_1227) True.intro);
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
                  let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i3;
                  Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                    let _atomic_wd_2_1 := _wd_1_0
                    exact h_1227) True.intro);
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
              obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
              exact _litex_checked_return _litex_input _litex_members _litex_guard));
            (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (by
              let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
              exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
              let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
              let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
              exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
              let _right := _atomic_wd_1_1
              exact (show Litex.Same _left _right from rfl)) h_1))))
          have h_2 : (by
            let _equal_wd_1_0 := _object_w50
            let _equal_wd_1_1 := _object_w51
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w50;
                  let _equal_wd_1_1 := _object_w51;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
                    let _norm := _equal_wd_1_0
                    let _expanded := (let _wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
                  let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i6)) (M.number (2 : ℂ)))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_2_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i6)) (M.number (2 : ℂ)))) _raw_i6) (Litex.denote (Litex.R (M := M))) := (by
                      intro _raw_i6 h_5423 _
                      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_5423)
                      have h_5423 : Litex.In _value_i6 _wd_2_0 := h_5423
                      have h_5424 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_5423).1
                            )
                        )
                      have h_5425 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_5423).2.1
                            )
                        )
                      have h_5426 : Litex.Le _value_i6 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_5423).2.2
                            )
                        )
                      have h_5427 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_2_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5423)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i6;
                        Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                          let _atomic_wd_2_1 := _wd_2_0
                          exact h_5423) True.intro);
                        (Litex.complexAbs _wd_4_0 (by
                          let _atomic_wd_2_0 := _wd_4_0
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                          let _atomic_wd_2_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                          (Litex.complexAbs _wd_4_0 (by
                            let _atomic_wd_3_0 := _wd_4_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i6;
                        Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                          let _atomic_wd_2_1 := _wd_2_0
                          exact h_5423) True.intro);
                        (Litex.complexAbs _wd_4_0 (by
                          let _atomic_wd_2_0 := _wd_4_0
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                          let _atomic_wd_2_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                          (Litex.complexAbs _wd_4_0 (by
                            let _atomic_wd_3_0 := _wd_4_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact (by
                          let _litex_power := _atomic_wd_1_0
                          have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_1_0).val.base)
                          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInR _litex_power _recorded_power_base
                        )))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)));
                  (Litex.sqrt _wd_1_0 (by
                    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
                    let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i6)) (M.number (2 : ℂ)))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_2_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i6)) (M.number (2 : ℂ)))) _raw_i6) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i6 h_6415 _
                        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_6415)
                        have h_6415 : Litex.In _value_i6 _wd_2_0 := h_6415
                        have h_6416 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_6415).1
                              )
                          )
                        have h_6417 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_6415).2.1
                              )
                          )
                        have h_6418 : Litex.Le _value_i6 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_6415).2.2
                              )
                          )
                        have h_6419 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_2_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6415)
                              )
                          )
                        change (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i6;
                          Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                            let _atomic_wd_3_1 := _wd_2_0
                            exact h_6415) True.intro);
                          (Litex.complexAbs _wd_4_0 (by
                            let _atomic_wd_3_0 := _wd_4_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                          let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                          (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                            let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                            (Litex.complexAbs _wd_4_0 (by
                              let _atomic_wd_4_0 := _wd_4_0
                              exact (by
                                let _litex_return_call := _atomic_wd_4_0
                                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                            exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i6;
                          Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                            let _atomic_wd_3_1 := _wd_2_0
                            exact h_6415) True.intro);
                          (Litex.complexAbs _wd_4_0 (by
                            let _atomic_wd_3_0 := _wd_4_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                          let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                          (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                            let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                            (Litex.complexAbs _wd_4_0 (by
                              let _atomic_wd_4_0 := _wd_4_0
                              exact (by
                                let _litex_return_call := _atomic_wd_4_0
                                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                            exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                          exact (by
                            let _litex_power := _atomic_wd_2_0
                            have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                            have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                            exact Litex.powStructuralInR _litex_power _recorded_power_base
                          )))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                    exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)) (by
                    let _atomic_wd_1_1 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
                    let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i6)) (M.number (2 : ℂ)))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_2_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i6)) (M.number (2 : ℂ)))) _raw_i6) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i6 h_7474 _
                        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_7474)
                        have h_7474 : Litex.In _value_i6 _wd_2_0 := h_7474
                        have h_7475 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_7474).1
                              )
                          )
                        have h_7476 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_7474).2.1
                              )
                          )
                        have h_7477 : Litex.Le _value_i6 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_7474).2.2
                              )
                          )
                        have h_7478 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_2_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_7474)
                              )
                          )
                        change (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i6;
                          Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                            let _atomic_wd_3_1 := _wd_2_0
                            exact h_7474) True.intro);
                          (Litex.complexAbs _wd_4_0 (by
                            let _atomic_wd_3_0 := _wd_4_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                          let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                          (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                            let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                            (Litex.complexAbs _wd_4_0 (by
                              let _atomic_wd_4_0 := _wd_4_0
                              exact (by
                                let _litex_return_call := _atomic_wd_4_0
                                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                            exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i6;
                          Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                            let _atomic_wd_3_1 := _wd_2_0
                            exact h_7474) True.intro);
                          (Litex.complexAbs _wd_4_0 (by
                            let _atomic_wd_3_0 := _wd_4_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                          let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                          (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                            let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                            (Litex.complexAbs _wd_4_0 (by
                              let _atomic_wd_4_0 := _wd_4_0
                              exact (by
                                let _litex_return_call := _atomic_wd_4_0
                                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                            exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                          exact (by
                            let _litex_power := _atomic_wd_2_0
                            have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                            have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                            exact Litex.powStructuralInR _litex_power _recorded_power_base
                          )))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                    exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
                    let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i3)) (M.number (2 : ℂ)))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (Litex.denote _wd_1_0) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → M.mem ((fun (_raw_i3 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i3)) (M.number (2 : ℂ)))) _raw_i3) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i3 h_1227 _
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1227)
                        have h_1227 : Litex.In _value_i3 _wd_1_0 := h_1227
                        have h_1228 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).1
                              )
                          )
                        have h_1229 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i3 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).2.1
                              )
                          )
                        have h_1230 : Litex.Le _value_i3 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).2.2
                              )
                          )
                        have h_1231 : Litex.In _value_i3 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_1_0 _value_i3 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1227)
                              )
                          )
                        change (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i3;
                          Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                            let _atomic_wd_2_1 := _wd_1_0
                            exact h_1227) True.intro);
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
                          let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i3;
                          Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                            let _atomic_wd_2_1 := _wd_1_0
                            exact h_1227) True.intro);
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
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                      let _left := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
                    let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i3)) (M.number (2 : ℂ)))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (Litex.denote _wd_1_0) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → M.mem ((fun (_raw_i3 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i3)) (M.number (2 : ℂ)))) _raw_i3) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i3 h_1227 _
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1227)
                        have h_1227 : Litex.In _value_i3 _wd_1_0 := h_1227
                        have h_1228 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).1
                              )
                          )
                        have h_1229 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i3 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).2.1
                              )
                          )
                        have h_1230 : Litex.Le _value_i3 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).2.2
                              )
                          )
                        have h_1231 : Litex.In _value_i3 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_1_0 _value_i3 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1227)
                              )
                          )
                        change (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i3;
                          Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                            let _atomic_wd_2_1 := _wd_1_0
                            exact h_1227) True.intro);
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
                          let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i3;
                          Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                            let _atomic_wd_2_1 := _wd_1_0
                            exact h_1227) True.intro);
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
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                      let _right := _atomic_wd_1_1
                      exact (show Litex.Same _left _right from rfl)) h_1))))
                    have _definition : Litex.Same _norm _expanded := Litex.euclideanNormFormula _norm (_expanded.val.arg).val.function (by rfl) (by rfl)
                    exact (_definition.trans (let _equal_wd_2_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
                  let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i6)) (M.number (2 : ℂ)))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_2_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i6)) (M.number (2 : ℂ)))) _raw_i6) (Litex.denote (Litex.R (M := M))) := (by
                      intro _raw_i6 h_5423 _
                      let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_5423)
                      have h_5423 : Litex.In _value_i6 _wd_2_0 := h_5423
                      have h_5424 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_5423).1
                            )
                        )
                      have h_5425 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_5423).2.1
                            )
                        )
                      have h_5426 : Litex.Le _value_i6 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_5423).2.2
                            )
                        )
                      have h_5427 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_2_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_5423)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i6;
                        Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                          let _atomic_wd_2_1 := _wd_2_0
                          exact h_5423) True.intro);
                        (Litex.complexAbs _wd_4_0 (by
                          let _atomic_wd_2_0 := _wd_4_0
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                          let _atomic_wd_2_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                          (Litex.complexAbs _wd_4_0 (by
                            let _atomic_wd_3_0 := _wd_4_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i6;
                        Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                          let _atomic_wd_2_1 := _wd_2_0
                          exact h_5423) True.intro);
                        (Litex.complexAbs _wd_4_0 (by
                          let _atomic_wd_2_0 := _wd_4_0
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                          let _atomic_wd_2_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                          (Litex.complexAbs _wd_4_0 (by
                            let _atomic_wd_3_0 := _wd_4_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact (by
                          let _litex_power := _atomic_wd_1_0
                          have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_1_0).val.base)
                          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInR _litex_power _recorded_power_base
                        )))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)));
                  (Litex.sqrt _wd_1_0 (by
                    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
                    let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i6)) (M.number (2 : ℂ)))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_2_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i6)) (M.number (2 : ℂ)))) _raw_i6) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i6 h_6415 _
                        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_6415)
                        have h_6415 : Litex.In _value_i6 _wd_2_0 := h_6415
                        have h_6416 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_6415).1
                              )
                          )
                        have h_6417 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_6415).2.1
                              )
                          )
                        have h_6418 : Litex.Le _value_i6 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_6415).2.2
                              )
                          )
                        have h_6419 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_2_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6415)
                              )
                          )
                        change (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i6;
                          Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                            let _atomic_wd_3_1 := _wd_2_0
                            exact h_6415) True.intro);
                          (Litex.complexAbs _wd_4_0 (by
                            let _atomic_wd_3_0 := _wd_4_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                          let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                          (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                            let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                            (Litex.complexAbs _wd_4_0 (by
                              let _atomic_wd_4_0 := _wd_4_0
                              exact (by
                                let _litex_return_call := _atomic_wd_4_0
                                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                            exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i6;
                          Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                            let _atomic_wd_3_1 := _wd_2_0
                            exact h_6415) True.intro);
                          (Litex.complexAbs _wd_4_0 (by
                            let _atomic_wd_3_0 := _wd_4_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                          let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                          (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                            let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                            (Litex.complexAbs _wd_4_0 (by
                              let _atomic_wd_4_0 := _wd_4_0
                              exact (by
                                let _litex_return_call := _atomic_wd_4_0
                                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                            exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                          exact (by
                            let _litex_power := _atomic_wd_2_0
                            have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                            have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                            exact Litex.powStructuralInR _litex_power _recorded_power_base
                          )))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                    exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)) (by
                    let _atomic_wd_1_1 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
                    let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i6)) (M.number (2 : ℂ)))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote _wd_2_0) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i6)) (M.number (2 : ℂ)))) _raw_i6) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i6 h_7474 _
                        let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_7474)
                        have h_7474 : Litex.In _value_i6 _wd_2_0 := h_7474
                        have h_7475 : Litex.In _value_i6 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_7474).1
                              )
                          )
                        have h_7476 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_7474).2.1
                              )
                          )
                        have h_7477 : Litex.Le _value_i6 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i6 h_7474).2.2
                              )
                          )
                        have h_7478 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_2_0 _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_7474)
                              )
                          )
                        change (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i6;
                          Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                            let _atomic_wd_3_1 := _wd_2_0
                            exact h_7474) True.intro);
                          (Litex.complexAbs _wd_4_0 (by
                            let _atomic_wd_3_0 := _wd_4_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                          let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                          (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                            let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                            (Litex.complexAbs _wd_4_0 (by
                              let _atomic_wd_4_0 := _wd_4_0
                              exact (by
                                let _litex_return_call := _atomic_wd_4_0
                                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                            exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i6;
                          Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                            let _atomic_wd_3_1 := _wd_2_0
                            exact h_7474) True.intro);
                          (Litex.complexAbs _wd_4_0 (by
                            let _atomic_wd_3_0 := _wd_4_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                          let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                          (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                            let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                            (Litex.complexAbs _wd_4_0 (by
                              let _atomic_wd_4_0 := _wd_4_0
                              exact (by
                                let _litex_return_call := _atomic_wd_4_0
                                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                            exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                          exact (by
                            let _litex_power := _atomic_wd_2_0
                            have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                            have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                            exact Litex.powStructuralInR _litex_power _recorded_power_base
                          )))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                    exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
                    let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i3)) (M.number (2 : ℂ)))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (Litex.denote _wd_1_0) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → M.mem ((fun (_raw_i3 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i3)) (M.number (2 : ℂ)))) _raw_i3) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i3 h_1227 _
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1227)
                        have h_1227 : Litex.In _value_i3 _wd_1_0 := h_1227
                        have h_1228 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).1
                              )
                          )
                        have h_1229 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i3 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).2.1
                              )
                          )
                        have h_1230 : Litex.Le _value_i3 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).2.2
                              )
                          )
                        have h_1231 : Litex.In _value_i3 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_1_0 _value_i3 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1227)
                              )
                          )
                        change (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i3;
                          Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                            let _atomic_wd_2_1 := _wd_1_0
                            exact h_1227) True.intro);
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
                          let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i3;
                          Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                            let _atomic_wd_2_1 := _wd_1_0
                            exact h_1227) True.intro);
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
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                      let _left := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
                    let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i3)) (M.number (2 : ℂ)))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (Litex.denote _wd_1_0) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → M.mem ((fun (_raw_i3 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i3)) (M.number (2 : ℂ)))) _raw_i3) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i3 h_1227 _
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1227)
                        have h_1227 : Litex.In _value_i3 _wd_1_0 := h_1227
                        have h_1228 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).1
                              )
                          )
                        have h_1229 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i3 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).2.1
                              )
                          )
                        have h_1230 : Litex.Le _value_i3 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).2.2
                              )
                          )
                        have h_1231 : Litex.In _value_i3 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_1_0 _value_i3 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1227)
                              )
                          )
                        change (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i3;
                          Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                            let _atomic_wd_2_1 := _wd_1_0
                            exact h_1227) True.intro);
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
                          let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i3;
                          Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                            let _atomic_wd_2_1 := _wd_1_0
                            exact h_1227) True.intro);
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
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                      let _right := _atomic_wd_1_1
                      exact (show Litex.Same _left _right from rfl)) h_1))));
                  let _equal_wd_2_1 := (let _wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
                  let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i4)) (M.number (2 : ℂ)))) _litex_input) (by
                    have _litex_checked_return : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _wd_2_0) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → M.mem ((fun (_raw_i4 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i4)) (M.number (2 : ℂ)))) _raw_i4) (Litex.denote (Litex.R (M := M))) := (by
                      intro _raw_i4 h_8473 _
                      let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_8473)
                      have h_8473 : Litex.In _value_i4 _wd_2_0 := h_8473
                      have h_8474 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i4 h_8473).1
                            )
                        )
                      have h_8475 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i4 h_8473).2.1
                            )
                        )
                      have h_8476 : Litex.Le _value_i4 _value_i1 :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangeBounds _wd_2_0 _value_i4 h_8473).2.2
                            )
                        )
                      have h_8477 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                        (by
                          litex_checked_step =>
                            exact (
                              (Litex.inClosedRangePositive _wd_2_0 _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_8473)
                            )
                        )
                      change (by
                        let _atomic_wd_1_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                        Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                          let _atomic_wd_2_1 := _wd_2_0
                          exact h_8473) True.intro);
                        (Litex.complexAbs _wd_4_0 (by
                          let _atomic_wd_2_0 := _wd_4_0
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                          let _atomic_wd_2_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                          (Litex.complexAbs _wd_4_0 (by
                            let _atomic_wd_3_0 := _wd_4_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                        Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                          let _atomic_wd_2_1 := _wd_2_0
                          exact h_8473) True.intro);
                        (Litex.complexAbs _wd_4_0 (by
                          let _atomic_wd_2_0 := _wd_4_0
                          exact (by
                            let _litex_return_call := _atomic_wd_2_0
                            exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                        let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                        (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                          let _atomic_wd_2_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                          (Litex.complexAbs _wd_4_0 (by
                            let _atomic_wd_3_0 := _wd_4_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                          exact (Litex.complexAbsInR _atomic_wd_2_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                        exact (by
                          let _litex_power := _atomic_wd_1_0
                          have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_1_0).val.base)
                          have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                          have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                          have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                          exact Litex.powStructuralInR _litex_power _recorded_power_base
                        )))
                    intro _litex_input _litex_domain
                    obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                    exact _litex_checked_return _litex_input _litex_members _litex_guard));
                  (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                    exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                    let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                    exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)));
                  (Litex.sqrt _wd_1_0 (by
                    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
                    let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i4)) (M.number (2 : ℂ)))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _wd_2_0) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → M.mem ((fun (_raw_i4 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i4)) (M.number (2 : ℂ)))) _raw_i4) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i4 h_9465 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_9465)
                        have h_9465 : Litex.In _value_i4 _wd_2_0 := h_9465
                        have h_9466 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i4 h_9465).1
                              )
                          )
                        have h_9467 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i4 h_9465).2.1
                              )
                          )
                        have h_9468 : Litex.Le _value_i4 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i4 h_9465).2.2
                              )
                          )
                        have h_9469 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_2_0 _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_9465)
                              )
                          )
                        change (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                          Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                            let _atomic_wd_3_1 := _wd_2_0
                            exact h_9465) True.intro);
                          (Litex.complexAbs _wd_4_0 (by
                            let _atomic_wd_3_0 := _wd_4_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                          let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                          (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                            let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                            (Litex.complexAbs _wd_4_0 (by
                              let _atomic_wd_4_0 := _wd_4_0
                              exact (by
                                let _litex_return_call := _atomic_wd_4_0
                                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                            exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                          Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                            let _atomic_wd_3_1 := _wd_2_0
                            exact h_9465) True.intro);
                          (Litex.complexAbs _wd_4_0 (by
                            let _atomic_wd_3_0 := _wd_4_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                          let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                          (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                            let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                            (Litex.complexAbs _wd_4_0 (by
                              let _atomic_wd_4_0 := _wd_4_0
                              exact (by
                                let _litex_return_call := _atomic_wd_4_0
                                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                            exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                          exact (by
                            let _litex_power := _atomic_wd_2_0
                            have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                            have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                            exact Litex.powStructuralInR _litex_power _recorded_power_base
                          )))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                    exact (Litex.finiteAggregateOnMember _atomic_wd_1_0 .real rfl)) (by
                    let _atomic_wd_1_1 := (let _wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
                    let _wd_2_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i4)) (M.number (2 : ℂ)))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote _wd_2_0) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → M.mem ((fun (_raw_i4 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i4)) (M.number (2 : ℂ)))) _raw_i4) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i4 h_10524 _
                        let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_10524)
                        have h_10524 : Litex.In _value_i4 _wd_2_0 := h_10524
                        have h_10525 : Litex.In _value_i4 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i4 h_10524).1
                              )
                          )
                        have h_10526 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i4 h_10524).2.1
                              )
                          )
                        have h_10527 : Litex.Le _value_i4 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_2_0 _value_i4 h_10524).2.2
                              )
                          )
                        have h_10528 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_2_0 _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_10524)
                              )
                          )
                        change (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                          Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                            let _atomic_wd_3_1 := _wd_2_0
                            exact h_10524) True.intro);
                          (Litex.complexAbs _wd_4_0 (by
                            let _atomic_wd_3_0 := _wd_4_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                          let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                          (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                            let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                            (Litex.complexAbs _wd_4_0 (by
                              let _atomic_wd_4_0 := _wd_4_0
                              exact (by
                                let _litex_return_call := _atomic_wd_4_0
                                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                            exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                          exact Litex.In _atomic_wd_2_0 (Litex.R (M := M)))
                        exact (by
                          let _atomic_wd_2_0 := (let _wd_3_0 := (let _wd_4_0 := (let _litex_call_arg_0 := _value_i4;
                          Litex.callOnDomain _wd_2_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                            let _atomic_wd_3_1 := _wd_2_0
                            exact h_10524) True.intro);
                          (Litex.complexAbs _wd_4_0 (by
                            let _atomic_wd_3_0 := _wd_4_0
                            exact (by
                              let _litex_return_call := _atomic_wd_3_0
                              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))));
                          let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
                          (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
                            let _atomic_wd_3_0 := (let _wd_4_0 := (_wd_3_0).val.arg;
                            (Litex.complexAbs _wd_4_0 (by
                              let _atomic_wd_4_0 := _wd_4_0
                              exact (by
                                let _litex_return_call := _atomic_wd_4_0
                                exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
                            exact (Litex.complexAbsInR _atomic_wd_3_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
                          exact (by
                            let _litex_power := _atomic_wd_2_0
                            have _elaborated_power_base := (Litex.complexAbsInR (_atomic_wd_2_0).val.base)
                            have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
                            have _recorded_power_base : Litex.In _litex_power.val.base (Litex.R (M := M)) := _elaborated_power_base
                            have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
                            exact Litex.powStructuralInR _litex_power _recorded_power_base
                          )))
                      intro _litex_input _litex_domain
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_2_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_2_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_2_0 _wd_2_1 _wd_2_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_2_0) (Litex.denote _litex_output) (Litex.isSet _wd_2_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      exact (Litex.closedRangeFinite _atomic_wd_2_0)) (by
                      let _atomic_wd_2_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      exact (Litex.subsetRefl _atomic_wd_2_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_2_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                    exact (Litex.leOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
                    let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i3)) (M.number (2 : ℂ)))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (Litex.denote _wd_1_0) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → M.mem ((fun (_raw_i3 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i3)) (M.number (2 : ℂ)))) _raw_i3) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i3 h_1227 _
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1227)
                        have h_1227 : Litex.In _value_i3 _wd_1_0 := h_1227
                        have h_1228 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).1
                              )
                          )
                        have h_1229 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i3 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).2.1
                              )
                          )
                        have h_1230 : Litex.Le _value_i3 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).2.2
                              )
                          )
                        have h_1231 : Litex.In _value_i3 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_1_0 _value_i3 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1227)
                              )
                          )
                        change (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i3;
                          Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                            let _atomic_wd_2_1 := _wd_1_0
                            exact h_1227) True.intro);
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
                          let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i3;
                          Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                            let _atomic_wd_2_1 := _wd_1_0
                            exact h_1227) True.intro);
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
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩))) _atomic_wd_1_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                      let _left := (let _wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19));
                    let _wd_1_1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i3)) (M.number (2 : ℂ)))) _litex_input) (by
                      have _litex_checked_return : ∀ (_raw_i3 : M.Value), M.mem _raw_i3 (Litex.denote _wd_1_0) → ((fun (_raw_i3 : M.Value) => True) _raw_i3) → M.mem ((fun (_raw_i3 : M.Value) => (M.powValue (Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i2) _raw_i3)) (M.number (2 : ℂ)))) _raw_i3) (Litex.denote (Litex.R (M := M))) := (by
                        intro _raw_i3 h_1227 _
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1227)
                        have h_1227 : Litex.In _value_i3 _wd_1_0 := h_1227
                        have h_1228 : Litex.In _value_i3 (Litex.Z (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).1
                              )
                          )
                        have h_1229 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i3 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).2.1
                              )
                          )
                        have h_1230 : Litex.Le _value_i3 _value_i1 :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangeBounds _wd_1_0 _value_i3 h_1227).2.2
                              )
                          )
                        have h_1231 : Litex.In _value_i3 (Litex.NPos (M := M)) :=
                          (by
                            litex_checked_step =>
                              exact (
                                (Litex.inClosedRangePositive _wd_1_0 _value_i3 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1227)
                              )
                          )
                        change (by
                          let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i3;
                          Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                            let _atomic_wd_2_1 := _wd_1_0
                            exact h_1227) True.intro);
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
                          let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (let _litex_call_arg_0 := _value_i3;
                          Litex.callOnDomain _wd_1_0 (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_28 (by
                            let _atomic_wd_2_1 := _wd_1_0
                            exact h_1227) True.intro);
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
                      obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote _wd_1_0) (Litex.denote (Litex.R (M := M))) (Litex.isSet _wd_1_0) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
                      exact _litex_checked_return _litex_input _litex_members _litex_guard));
                    (Litex.finiteAggregateOn false _wd_1_0 _wd_1_1 _wd_1_0 (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote _wd_1_0) (Litex.denote _litex_output) (Litex.isSet _wd_1_0) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      exact (Litex.closedRangeFinite _atomic_wd_1_0)) (by
                      let _atomic_wd_1_0 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_19))
                      exact (Litex.subsetRefl _atomic_wd_1_1)) (Litex.subsetOfForall (Litex.R (M := M)) (Litex.C (M := M)) (fun _a _ha => (Litex.realToComplex _a _ha))) (Litex.formulaFnInFnSet _wd_1_1) (fun x hx => (Litex.SetSemantics.sep_members _ _ _).mpr ⟨hx, True.intro⟩)))
                      let _right := _atomic_wd_1_1
                      exact (show Litex.Same _left _right from rfl)) h_1))));
                  (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (by
                    let _left := _equal_wd_2_0
                    let _right := _equal_wd_2_1
                    exact (show Litex.Same _left _right from rfl)))))
                  )))
                )
            )
          exact h_2
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_euclidean_x5f_norm_x5f_definition_x2f_statement_x2e_lit
