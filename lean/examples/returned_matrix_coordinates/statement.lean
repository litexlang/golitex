import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_returned_x5f_matrix_x5f_coordinates_x2f_statement_x2e_lit

universe u v1 v3 v4 v5
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_131 : Litex.In _value_i1 (let _checked_header : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.R (M := M))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → True := (by
    intro _raw_i2 h_123 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_123)
    have h_123 : Litex.In _value_i2 (Litex.R (M := M)) := h_123
    exact True.intro);
  Litex.fnSet (let _litex_output := (Litex.matrixSet (Litex.R (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num))); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.R (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.R (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_132 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_143 : Litex.In _value_i4 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_170 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))), (by
  let _object_w17 := (by
    let _returned_receiver := (let _litex_call_arg_0 := _value_i3;
  Litex.callOnDomain (Litex.R (M := M)) (Litex.matrixSet (Litex.R (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_131 h_132 True.intro)
    let _returned_array := (Litex.matrixSet (Litex.R (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)))
    let _returned_signature := Litex.matrixSignature _returned_array
    let _returned_argument := (Litex.callArguments2 _value_i4 _value_i5)
    have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := Litex.callOnInOutput _returned_receiver
    have _returned_domain : M.mem (Litex.denote _returned_argument) _returned_signature.domain := (Litex.SetSemantics.sep_members _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _value_i4 _value_i5 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
    exact h_143) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
    exact h_170)), True.intro⟩
    exact Litex.callOn _returned_signature _returned_receiver _returned_argument _returned_member _returned_domain)
  exact (by
    let _atomic_wd_1_0 := _object_w17
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_131 _Host_i3 _rep_i3 _value_i3 h_132 _Host_i4 _rep_i4 _value_i4 h_143 _Host_i5 _rep_i5 _value_i5 h_170
          have h_144 : Litex.In _value_i4 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 h_143).1
                )
            )
          have h_145 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 h_143).2.1
                )
            )
          have h_146 : Litex.Le _value_i4 (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 h_143).2.2
                )
            )
          have h_147 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_143)
                )
            )
          have h_171 : Litex.In _value_i5 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i5 h_170).1
                )
            )
          have h_172 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i5 h_170).2.1
                )
            )
          have h_173 : Litex.Le _value_i5 (Litex.number (M := M) (3 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i5 h_170).2.2
                )
            )
          have h_174 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_170)
                )
            )
          let _object_w17 := (by
            let _returned_receiver := (let _litex_call_arg_0 := _value_i3;
          Litex.callOnDomain (Litex.R (M := M)) (Litex.matrixSet (Litex.R (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _value_i1 _litex_call_arg_0 h_131 h_132 True.intro)
            let _returned_array := (Litex.matrixSet (Litex.R (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)))
            let _returned_signature := Litex.matrixSignature _returned_array
            let _returned_argument := (Litex.callArguments2 _value_i4 _value_i5)
            have _returned_member : Litex.In _returned_receiver (Litex.fnSet _returned_signature) := Litex.callOnInOutput _returned_receiver
            have _returned_domain : M.mem (Litex.denote _returned_argument) _returned_signature.domain := (Litex.SetSemantics.sep_members _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _value_i4 _value_i5 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact h_143) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
            exact h_170)), True.intro⟩
            exact Litex.callOn _returned_signature _returned_receiver _returned_argument _returned_member _returned_domain)
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w17
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w17
                    exact (by
                      let _litex_return_call := _atomic_wd_1_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callOnInOutput _litex_return_call)))
                )
            )
          exact h_1
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_returned_x5f_matrix_x5f_coordinates_x2f_statement_x2e_lit
