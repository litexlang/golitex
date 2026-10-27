import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_returned_x5f_finite_x5f_sequence_x5f_values_x2f_statement_x2e_lit

universe u v1 v3 v4 v9 v10 v12 v13
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_86 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.R (M := M))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_81 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_81)
    have h_81 : Litex.In _value_i2 (Litex.R (M := M)) := h_81
    exact True.intro);
  Litex.fnSet (let _litex_output := (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_87 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_98 : Litex.In _value_i4 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))), (by
  let _object_w15 := (by
    let _returned_receiver := (let _litex_call_arg_0 := _value_i3;
  Litex.callOnDomain (Litex.R (M := M)) (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_86 h_87 True.intro)
    let _returned_array := (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)))
    let _returned_signature := Litex.finiteSeqSignature _returned_array
    let _returned_argument := _value_i4
    have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := Litex.callOnInOutput _returned_receiver
    have _returned_domain : M.mem (Litex.denote _returned_argument) _returned_signature.domain := (Litex.SetSemantics.sep_members _ _ _).mpr ⟨(by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
    exact h_98), True.intro⟩
    exact Litex.callOn _returned_signature _returned_receiver _returned_argument _returned_member _returned_domain)
  exact (by
    let _atomic_wd_1_0 := _object_w15
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_86 _Host_i3 _rep_i3 _value_i3 h_87 _Host_i4 _rep_i4 _value_i4 h_98
          have h_99 : Litex.In _value_i4 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 h_98).1
                )
            )
          have h_100 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 h_98).2.1
                )
            )
          have h_101 : Litex.Le _value_i4 (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 h_98).2.2
                )
            )
          have h_102 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_98)
                )
            )
          let _object_w15 := (by
            let _returned_receiver := (let _litex_call_arg_0 := _value_i3;
          Litex.callOnDomain (Litex.R (M := M)) (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_86 h_87 True.intro)
            let _returned_array := (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)))
            let _returned_signature := Litex.finiteSeqSignature _returned_array
            let _returned_argument := _value_i4
            have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := Litex.callOnInOutput _returned_receiver
            have _returned_domain : M.mem (Litex.denote _returned_argument) _returned_signature.domain := (Litex.SetSemantics.sep_members _ _ _).mpr ⟨(by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
            exact h_98), True.intro⟩
            exact Litex.callOn _returned_signature _returned_receiver _returned_argument _returned_member _returned_domain)
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w15
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w15
                    exact (by
                      let _litex_return_call := _atomic_wd_1_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callOnInOutput _litex_return_call)))
                )
            )
          exact h_1
        )
      )
  )

theorem h_227 : ∀ {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_259 : Litex.In _value_i9 (Litex.N (M := M))) {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_270 : Litex.In _value_i10 (let _checked_header : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (Litex.denote (Litex.R (M := M))) → ((fun (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) _raw_i11) → True := (by
    intro _raw_i11 h_261 h_224
    let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_261)
    have h_261 : Litex.In _value_i11 (Litex.R (M := M)) := h_261
    have h_224 : ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i11 = (M.number (0 : ℂ))))
              exact h_224)
          )
      )
    exact True.intro);
  Litex.fnSet (let _litex_output := (Litex.finiteSeq (Litex.R (M := M)) _value_i9 (Litex.isSet (Litex.R (M := M))) h_259); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) _litex_input)))) {_Host_i12 : Type v12} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_271 : Litex.In _value_i12 (Litex.R (M := M))) {_Host_i13 : Type v13} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_295 : Litex.In _value_i13 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i9 h_259))) (h_225 : ¬ Litex.Same _value_i12 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_w27 := (by
    let _returned_receiver := (let _litex_call_arg_0 := _value_i12;
  Litex.callOnDomain (Litex.R (M := M)) (Litex.finiteSeq (Litex.R (M := M)) _value_i9 (Litex.isSet (Litex.R (M := M))) h_259) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) _litex_input) _value_i10 _litex_call_arg_0 h_270 h_271 h_225)
    let _returned_array := (Litex.finiteSeq (Litex.R (M := M)) _value_i9 (Litex.isSet (Litex.R (M := M))) h_259)
    let _returned_signature := Litex.finiteSeqSignature _returned_array
    let _returned_argument := _value_i13
    have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := Litex.callOnInOutput _returned_receiver
    have _returned_domain : M.mem (Litex.denote _returned_argument) _returned_signature.domain := (Litex.SetSemantics.sep_members _ _ _).mpr ⟨(by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i9 h_259))
    exact h_295), True.intro⟩
    exact Litex.callOn _returned_signature _returned_receiver _returned_argument _returned_member _returned_domain)
  exact (by
    let _atomic_wd_1_0 := _object_w27
    exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i9 _rep_i9 _value_i9 h_259 _Host_i10 _rep_i10 _value_i10 h_270 _Host_i12 _rep_i12 _value_i12 h_271 _Host_i13 _rep_i13 _value_i13 h_295 h_225
          have h_260 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i9 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i9 h_259)
                )
            )
          have h_296 : Litex.In _value_i13 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i9 h_259)) _value_i13 h_295).1
                )
            )
          have h_297 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i13 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i9 h_259)) _value_i13 h_295).2.1
                )
            )
          have h_298 : Litex.Le _value_i13 _value_i9 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i9 h_259)) _value_i13 h_295).2.2
                )
            )
          have h_299 : Litex.In _value_i13 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i9 h_259)) _value_i13 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_295)
                )
            )
          let _object_w27 := (by
            let _returned_receiver := (let _litex_call_arg_0 := _value_i12;
          Litex.callOnDomain (Litex.R (M := M)) (Litex.finiteSeq (Litex.R (M := M)) _value_i9 (Litex.isSet (Litex.R (M := M))) h_259) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => (¬ (_raw_i11 = (M.number (0 : ℂ))))) _litex_input) _value_i10 _litex_call_arg_0 h_270 h_271 h_225)
            let _returned_array := (Litex.finiteSeq (Litex.R (M := M)) _value_i9 (Litex.isSet (Litex.R (M := M))) h_259)
            let _returned_signature := Litex.finiteSeqSignature _returned_array
            let _returned_argument := _value_i13
            have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := Litex.callOnInOutput _returned_receiver
            have _returned_domain : M.mem (Litex.denote _returned_argument) _returned_signature.domain := (Litex.SetSemantics.sep_members _ _ _).mpr ⟨(by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i9 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i9 h_259))
            exact h_295), True.intro⟩
            exact Litex.callOn _returned_signature _returned_receiver _returned_argument _returned_member _returned_domain)
          have h_226 : (by
            let _atomic_wd_1_0 := _object_w27
            exact Litex.In _atomic_wd_1_0 (Litex.C (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w27
                    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))
                )
            )
          exact h_226
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_returned_x5f_finite_x5f_sequence_x5f_values_x2f_statement_x2e_lit
