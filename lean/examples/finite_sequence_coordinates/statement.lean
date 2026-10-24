import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_sequence_x5f_coordinates_x2f_statement_x2e_lit

universe u v1 v2 v3 v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_21 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_22 : Litex.In _value_i2 (Litex.N (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_32 : Litex.In _value_i3 (Litex.finiteSeq _value_i1 _value_i2 h_21 h_22)) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_57 : Litex.In _value_i4 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))), (by
  let _object_h33 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq _value_i1 _value_i2 h_21 h_22)))
  have h_33 : Litex.In _value_i3 _object_h33 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i3 _value_i3 (Litex.finiteSeq _value_i1 _value_i2 h_21 h_22) _object_h33 (Litex.sameRefl _value_i3) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq _value_i1 _value_i2 h_21 h_22)) h_32)
        )
    )
  let _object_w9 := (let _litex_call_arg_0 := _value_i4;
  Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22)) _value_i1 (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_33 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
    exact h_57) True.intro)
  exact (by
    let _atomic_wd_1_0 := _object_w9
    exact Litex.In _atomic_wd_1_0 _value_i1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_21 _Host_i2 _rep_i2 _value_i2 h_22 _Host_i3 _rep_i3 _value_i3 h_32 _Host_i4 _rep_i4 _value_i4 h_57
          have h_23 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_22)
                )
            )
          let _object_h33 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq _value_i1 _value_i2 h_21 h_22)))
          have h_33 : Litex.In _value_i3 _object_h33 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i3 _value_i3 (Litex.finiteSeq _value_i1 _value_i2 h_21 h_22) _object_h33 (Litex.sameRefl _value_i3) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq _value_i1 _value_i2 h_21 h_22)) h_32)
                )
            )
          have h_58 : Litex.In _value_i4 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22)) _value_i4 h_57).1
                )
            )
          have h_59 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22)) _value_i4 h_57).2.1
                )
            )
          have h_60 : Litex.Le _value_i4 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22)) _value_i4 h_57).2.2
                )
            )
          have h_61 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22)) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_57)
                )
            )
          let _object_w9 := (let _litex_call_arg_0 := _value_i4;
          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22)) _value_i1 (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_33 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_22))
            exact h_57) True.intro)
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w9
            exact Litex.In _atomic_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w9
                    exact (by
                      let _litex_return_call := _atomic_wd_1_0
                      exact Litex.inOfSame _litex_return_call _litex_return_call _value_i1 _value_i1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _value_i1) (Litex.callOnInOutput _litex_return_call)))
                )
            )
          exact h_1
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_sequence_x5f_coordinates_x2f_statement_x2e_lit
