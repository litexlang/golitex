import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_adjugate_x5f_coordinates_x2f_statement_x2e_lit

universe u v1 v2 v3 v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_25 : Litex.In _value_i1 (Litex.NPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_50 : Litex.In _value_i2 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) (Litex.inNPos_natural _value_i1 h_25) (Litex.inNPos_natural _value_i1 h_25))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_80 : Litex.In _value_i3 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_25)))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_85 : Litex.In _value_i4 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_25)))), (by
  let _object_w8 := (let _litex_matrix_head := (Litex.matrixAdjugate _value_i2 _value_i1 (Litex.inNPos_natural _value_i1 h_25) (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) (Litex.inNPos_natural _value_i1 h_25) (Litex.inNPos_natural _value_i1 h_25))
    exact h_50));
  (let _litex_call_arg_0 := _value_i3;
  let _litex_call_arg_1 := _value_i4;
  Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.order (_litex_matrix_head).val.order .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixAdjugateInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_25)))
    exact h_80) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_25)))
    exact h_85)), True.intro⟩)))
  let _object_w9 := (Litex.matrixCofactor _value_i2 _value_i1 _value_i4 _value_i3 h_25 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_25)))
    exact h_85) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_25)))
    exact h_80) (Litex.inNPos_natural _value_i1 h_25) (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) (Litex.inNPos_natural _value_i1 h_25) (Litex.inNPos_natural _value_i1 h_25))
    exact h_50))
  exact (by
    let _equal_wd_1_0 := _object_w8
    let _equal_wd_1_1 := _object_w9
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_25 _Host_i2 _rep_i2 _value_i2 h_50 _Host_i3 _rep_i3 _value_i3 h_80 _Host_i4 _rep_i4 _value_i4 h_85
          have h_26 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inNPos_positive _value_i1 h_25)
                )
            )
          have h_27 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i1 h_26)
                )
            )
          have h_28 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i1 h_26) _litex_zero.symm)
                )
            )
          let _object_h51 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) (Litex.inNPos_natural _value_i1 h_25) (Litex.inNPos_natural _value_i1 h_25))))
          have h_51 : Litex.In _value_i2 _object_h51 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i2 _value_i2 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) (Litex.inNPos_natural _value_i1 h_25) (Litex.inNPos_natural _value_i1 h_25)) _object_h51 (Litex.sameRefl _value_i2) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) (Litex.inNPos_natural _value_i1 h_25) (Litex.inNPos_natural _value_i1 h_25)))) h_50)
                )
            )
          have h_81 : Litex.In _value_i3 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_25))) _value_i3 h_80).1
                )
            )
          have h_82 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_25))) _value_i3 h_80).2.1
                )
            )
          have h_83 : Litex.Le _value_i3 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_25))) _value_i3 h_80).2.2
                )
            )
          have h_84 : Litex.In _value_i3 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_25))) _value_i3 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_80)
                )
            )
          have h_86 : Litex.In _value_i4 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_25))) _value_i4 h_85).1
                )
            )
          have h_87 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_25))) _value_i4 h_85).2.1
                )
            )
          have h_88 : Litex.Le _value_i4 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_25))) _value_i4 h_85).2.2
                )
            )
          have h_89 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_25))) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_85)
                )
            )
          let _object_w8 := (let _litex_matrix_head := (Litex.matrixAdjugate _value_i2 _value_i1 (Litex.inNPos_natural _value_i1 h_25) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) (Litex.inNPos_natural _value_i1 h_25) (Litex.inNPos_natural _value_i1 h_25))
            exact h_50));
          (let _litex_call_arg_0 := _value_i3;
          let _litex_call_arg_1 := _value_i4;
          Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.order (_litex_matrix_head).val.order .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixAdjugateInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_25)))
            exact h_80) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_25)))
            exact h_85)), True.intro⟩)))
          let _object_w9 := (Litex.matrixCofactor _value_i2 _value_i1 _value_i4 _value_i3 h_25 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_25)))
            exact h_85) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_25)))
            exact h_80) (Litex.inNPos_natural _value_i1 h_25) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) (Litex.inNPos_natural _value_i1 h_25) (Litex.inNPos_natural _value_i1 h_25))
            exact h_50))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w8
            let _equal_wd_1_1 := _object_w9
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w8;
                  let _equal_wd_1_1 := _object_w9;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((show Litex.denote _equal_wd_1_0 = (Litex.matrixCofactorValue (Litex.denote ((_equal_wd_1_0).val.function).val.matrix) ((_equal_wd_1_0).val.function).val.order (Litex.denote _value_i4) (Litex.denote _value_i3)) from by
                    have h := (congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote (Litex.callArguments2 _value_i3 _value_i4))) (show @Eq M.Value _ _ from Eq.refl _)).trans (Litex.matrixAdjugateCall (_equal_wd_1_0).val.function (Litex.denote (Litex.callArguments2 _value_i3 _value_i4)) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_25)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_25))))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_25))))
                    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_25))))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  ))) (fun (_litex_input : M.Value) => (fun (_raw_i23 : M.Value) (_raw_i24 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 _value_i3 _value_i4))).mpr ⟨(Litex.callArguments2_mem_cart _value_i3 _value_i4 (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_25)))
                    exact h_80) (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_25)))
                    exact h_85)), True.intro⟩))
                    change Litex.denote _equal_wd_1_0 = Litex.matrixAdjugateBody (Litex.denote ((_equal_wd_1_0).val.function).val.matrix) ((_equal_wd_1_0).val.function).val.order (Litex.FiniteFunction.pack2 (Litex.denote _value_i3) (Litex.denote _value_i4)) at h
                    unfold Litex.matrixAdjugateBody at h
                    rw [Litex.FiniteFunction.unpack_pack2] at h
                    exact h).trans (show (Litex.matrixCofactorValue (Litex.denote ((_equal_wd_1_0).val.function).val.matrix) ((_equal_wd_1_0).val.function).val.order (Litex.denote _value_i4) (Litex.denote _value_i3)) = (Litex.denote _equal_wd_1_1) from rfl)).trans (show @Eq M.Value _ _ from Eq.refl _))))
                )
            )
          exact h_1
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_adjugate_x5f_coordinates_x2f_statement_x2e_lit
