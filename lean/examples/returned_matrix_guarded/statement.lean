import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_returned_x5f_matrix_x5f_guarded_x2f_statement_x2e_lit

universe u v1 v2 v3 v5 v6 v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_40 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_42 : Litex.In _value_i2 (Litex.N (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_62 : Litex.In _value_i3 (let _checked_header : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote (Litex.R (M := M))) → ((fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _raw_i4) → True := (by
    intro _raw_i4 h_44 h_1
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_44)
    have h_44 : Litex.In _value_i4 (Litex.R (M := M)) := h_44
    have h_1 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i4 = (M.number (0 : ℂ))))
              exact h_1)
          )
      )
    exact True.intro);
  Litex.fnSet (let _litex_output := (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_40 h_42); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _litex_input)))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_63 : Litex.In _value_i5 (Litex.R (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_92 : Litex.In _value_i6 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_40))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_141 : Litex.In _value_i7 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_42))) (h_2 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_w13 := (by
    let _returned_receiver := (let _litex_call_arg_0 := _value_i5;
  Litex.callOnDomain (Litex.R (M := M)) (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_40 h_42) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _litex_input) _value_i3 _litex_call_arg_0 h_62 h_63 h_2)
    let _returned_array := (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_40 h_42)
    let _returned_signature := Litex.matrixSignature _returned_array
    let _returned_argument := (Litex.callArguments2 _value_i6 _value_i7)
    have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := Litex.callOnInOutput _returned_receiver
    have _returned_domain : M.mem (Litex.denote _returned_argument) _returned_signature.domain := (Litex.SetSemantics.sep_members _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _value_i6 _value_i7 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_40))
    exact h_92) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_42))
    exact h_141)), True.intro⟩
    exact Litex.callOn _returned_signature _returned_receiver _returned_argument _returned_member _returned_domain)
  exact (by
    let _atomic_wd_1_0 := _object_w13
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_40 _Host_i2 _rep_i2 _value_i2 h_42 _Host_i3 _rep_i3 _value_i3 h_62 _Host_i5 _rep_i5 _value_i5 h_63 _Host_i6 _rep_i6 _value_i6 h_92 _Host_i7 _rep_i7 _value_i7 h_141 h_2
          have h_41 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_40)
                )
            )
          have h_43 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_42)
                )
            )
          have h_93 : Litex.In _value_i6 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_40)) _value_i6 h_92).1
                )
            )
          have h_94 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_40)) _value_i6 h_92).2.1
                )
            )
          have h_95 : Litex.Le _value_i6 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_40)) _value_i6 h_92).2.2
                )
            )
          have h_96 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_40)) _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_92)
                )
            )
          have h_142 : Litex.In _value_i7 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_42)) _value_i7 h_141).1
                )
            )
          have h_143 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_42)) _value_i7 h_141).2.1
                )
            )
          have h_144 : Litex.Le _value_i7 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_42)) _value_i7 h_141).2.2
                )
            )
          have h_145 : Litex.In _value_i7 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_42)) _value_i7 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_141)
                )
            )
          let _object_w13 := (by
            let _returned_receiver := (let _litex_call_arg_0 := _value_i5;
          Litex.callOnDomain (Litex.R (M := M)) (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_40 h_42) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => (¬ (_raw_i4 = (M.number (0 : ℂ))))) _litex_input) _value_i3 _litex_call_arg_0 h_62 h_63 h_2)
            let _returned_array := (Litex.matrixSet (Litex.R (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.R (M := M))) h_40 h_42)
            let _returned_signature := Litex.matrixSignature _returned_array
            let _returned_argument := (Litex.callArguments2 _value_i6 _value_i7)
            have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := Litex.callOnInOutput _returned_receiver
            have _returned_domain : M.mem (Litex.denote _returned_argument) _returned_signature.domain := (Litex.SetSemantics.sep_members _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _value_i6 _value_i7 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_40))
            exact h_92) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_42))
            exact h_141)), True.intro⟩
            exact Litex.callOn _returned_signature _returned_receiver _returned_argument _returned_member _returned_domain)
          have h_3 : (by
            let _atomic_wd_1_0 := _object_w13
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w13
                    exact (by
                      let _litex_return_call := _atomic_wd_1_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callOnInOutput _litex_return_call)))
                )
            )
          exact h_3
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_returned_x5f_matrix_x5f_guarded_x2f_statement_x2e_lit
