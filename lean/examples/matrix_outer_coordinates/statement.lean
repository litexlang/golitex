import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_outer_x5f_coordinates_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_27 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_29 : Litex.In _value_i2 (Litex.N (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_37 : Litex.In _value_i3 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_27)) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_47 : Litex.In _value_i4 (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_29)) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_87 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_27))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_146 : Litex.In _value_i6 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_29))), (by
  let _object_h38 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_27)))
  have h_38 : Litex.In _value_i3 _object_h38 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i3 _value_i3 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_27) _object_h38 (Litex.sameRefl _value_i3) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_27)) h_37)
        )
    )
  let _object_h48 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_29)))
  have h_48 : Litex.In _value_i4 _object_h48 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i4 _value_i4 (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_29) _object_h48 (Litex.sameRefl _value_i4) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_29)) h_47)
        )
    )
  let _object_w12 := (let _litex_matrix_head := (Litex.matrixOuter _value_i3 _value_i4 _value_i1 _value_i2 h_27 h_29 (by
    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_27)
    exact h_37) (by
    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_29)
    exact h_47));
  (let _litex_call_arg_0 := _value_i5;
  let _litex_call_arg_1 := _value_i6;
  Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixOuterInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_27))
    exact h_87) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_29))
    exact h_146)), True.intro⟩)))
  let _object_w13 := (let _wd_1_0 := (let _litex_call_arg_0 := _value_i5;
  Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_27)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_38 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_27))
    exact h_87) True.intro);
  let _wd_1_1 := (let _litex_call_arg_0 := _value_i6;
  Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_29)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_48 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_29))
    exact h_146) True.intro);
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
  exact (by
    let _equal_wd_1_0 := _object_w12
    let _equal_wd_1_1 := _object_w13
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_27 _Host_i2 _rep_i2 _value_i2 h_29 _Host_i3 _rep_i3 _value_i3 h_37 _Host_i4 _rep_i4 _value_i4 h_47 _Host_i5 _rep_i5 _value_i5 h_87 _Host_i6 _rep_i6 _value_i6 h_146
          have h_28 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_27)
                )
            )
          have h_30 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_29)
                )
            )
          let _object_h38 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_27)))
          have h_38 : Litex.In _value_i3 _object_h38 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i3 _value_i3 (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_27) _object_h38 (Litex.sameRefl _value_i3) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_27)) h_37)
                )
            )
          let _object_h48 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_29)))
          have h_48 : Litex.In _value_i4 _object_h48 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i4 _value_i4 (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_29) _object_h48 (Litex.sameRefl _value_i4) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_29)) h_47)
                )
            )
          have h_88 : Litex.In _value_i5 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_27)) _value_i5 h_87).1
                )
            )
          have h_89 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_27)) _value_i5 h_87).2.1
                )
            )
          have h_90 : Litex.Le _value_i5 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_27)) _value_i5 h_87).2.2
                )
            )
          have h_91 : Litex.In _value_i5 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_27)) _value_i5 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_87)
                )
            )
          have h_147 : Litex.In _value_i6 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_29)) _value_i6 h_146).1
                )
            )
          have h_148 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_29)) _value_i6 h_146).2.1
                )
            )
          have h_149 : Litex.Le _value_i6 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_29)) _value_i6 h_146).2.2
                )
            )
          have h_150 : Litex.In _value_i6 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_29)) _value_i6 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_146)
                )
            )
          let _object_w12 := (let _litex_matrix_head := (Litex.matrixOuter _value_i3 _value_i4 _value_i1 _value_i2 h_27 h_29 (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_27)
            exact h_37) (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_29)
            exact h_47));
          (let _litex_call_arg_0 := _value_i5;
          let _litex_call_arg_1 := _value_i6;
          Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.rows (_litex_matrix_head).val.cols .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixOuterInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_27))
            exact h_87) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_29))
            exact h_146)), True.intro⟩)))
          let _object_w13 := (let _wd_1_0 := (let _litex_call_arg_0 := _value_i5;
          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_27)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_38 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_27))
            exact h_87) True.intro);
          let _wd_1_1 := (let _litex_call_arg_0 := _value_i6;
          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_29)) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_48 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_29))
            exact h_146) True.intro);
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              let _litex_return_call := _atomic_wd_1_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (by
              let _litex_return_call := _atomic_wd_1_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w12
            let _equal_wd_1_1 := _object_w13
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w12;
                  let _equal_wd_1_1 := _object_w13;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((show Litex.denote _equal_wd_1_0 = (M.mulValue (Litex.FunctionSemantics.callValue (Litex.denote ((_equal_wd_1_0).val.function).val.left) (Litex.denote _value_i5)) (Litex.FunctionSemantics.callValue (Litex.denote ((_equal_wd_1_0).val.function).val.right) (Litex.denote _value_i6))) from by
                    have h := (congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote (Litex.callArguments2 _value_i5 _value_i6))) (show @Eq M.Value _ _ from Eq.refl _)).trans (Litex.matrixOuterCall (_equal_wd_1_0).val.function (Litex.denote (Litex.callArguments2 _value_i5 _value_i6)) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_27))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_29)))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_27)))
                    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_29)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  ))) (fun (_litex_input : M.Value) => (fun (_raw_i32 : M.Value) (_raw_i33 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 _value_i5 _value_i6))).mpr ⟨(Litex.callArguments2_mem_cart _value_i5 _value_i6 (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 h_27))
                    exact h_87) (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i2 h_29))
                    exact h_146)), True.intro⟩))
                    change Litex.denote _equal_wd_1_0 = Litex.matrixOuterBody (Litex.denote ((_equal_wd_1_0).val.function).val.left) (Litex.denote ((_equal_wd_1_0).val.function).val.right) (Litex.FiniteFunction.pack2 (Litex.denote _value_i5) (Litex.denote _value_i6)) at h
                    dsimp only [Litex.matrixOuterBody] at h
                    rw [Litex.FiniteFunction.unpack_pack2] at h
                    exact h).trans (show (M.mulValue (Litex.FunctionSemantics.callValue (Litex.denote ((_equal_wd_1_0).val.function).val.left) (Litex.denote _value_i5)) (Litex.FunctionSemantics.callValue (Litex.denote ((_equal_wd_1_0).val.function).val.right) (Litex.denote _value_i6))) = (Litex.denote _equal_wd_1_1) from rfl)).trans (show @Eq M.Value _ _ from Eq.refl _))))
                )
            )
          exact h_1
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_outer_x5f_coordinates_x2f_statement_x2e_lit
