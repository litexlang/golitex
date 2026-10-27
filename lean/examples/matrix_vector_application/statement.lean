import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_vector_x5f_application_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v14 v15 v16 v17
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_22 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_24 : Litex.In _value_i2 (Litex.N (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_39 : Litex.In _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_22 h_24)) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_49 : Litex.In _value_i4 (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_24)), (by
  let _object_w12 := (Litex.matrixApply _value_i3 _value_i4 _value_i1 _value_i2 h_22 h_24 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_22 h_24)
    exact h_39) (by
    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_24)
    exact h_49))
  let _object_w13 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_22)
  exact (by
    let _atomic_wd_1_0 := _object_w12
    let _atomic_wd_1_1 := _object_w13
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_22 _Host_i2 _rep_i2 _value_i2 h_24 _Host_i3 _rep_i3 _value_i3 h_39 _Host_i4 _rep_i4 _value_i4 h_49
          have h_23 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_22)
                )
            )
          have h_25 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_24)
                )
            )
          let _object_h40 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_22 h_24)))
          have h_40 : Litex.In _value_i3 _object_h40 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_22 h_24) _object_h40 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_22 h_24))) h_39)
                )
            )
          let _object_h50 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_24)))
          have h_50 : Litex.In _value_i4 _object_h50 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i4 _value_i4 (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_24) _object_h50 (Litex.sameRefl _value_i4) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_24)) h_49)
                )
            )
          let _object_w12 := (Litex.matrixApply _value_i3 _value_i4 _value_i1 _value_i2 h_22 h_24 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_22 h_24)
            exact h_39) (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i2 (Litex.isSet (Litex.C (M := M))) h_24)
            exact h_49))
          let _object_w13 := (Litex.finiteSeq (Litex.C (M := M)) _value_i1 (Litex.isSet (Litex.C (M := M))) h_22)
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w12
            let _atomic_wd_1_1 := _object_w13
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w12
                    let _atomic_wd_1_1 := _object_w13
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixApplySignature (_litex_matrix).val.rows .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixApplyInFnSet _litex_matrix))))
                )
            )
          let _object_h236 := (Litex.fnSet (Litex.finiteSeqSignature _object_w13))
          have h_236 : Litex.In _object_w12 _object_h236 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _object_w12 _object_w12 _object_w13 _object_h236 (Litex.sameRefl _object_w12) (Litex.finiteSeq_eq_fnSet _object_w13) h_1)
                )
            )
          exact h_1
        )
      )
  )

theorem h_238 : ∀ {_Host_i14 : Type v14} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_258 : Litex.In _value_i14 (Litex.N (M := M))) {_Host_i15 : Type v15} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_260 : Litex.In _value_i15 (Litex.N (M := M))) {_Host_i16 : Type v16} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_275 : Litex.In _value_i16 (Litex.matrixSet (Litex.R (M := M)) _value_i14 _value_i15 (Litex.isSet (Litex.R (M := M))) h_258 h_260)) {_Host_i17 : Type v17} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_285 : Litex.In _value_i17 (Litex.finiteSeq (Litex.R (M := M)) _value_i15 (Litex.isSet (Litex.R (M := M))) h_260)), (by
  let _object_h276 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i14 _value_i15 (Litex.isSet (Litex.R (M := M))) h_258 h_260)))
  have h_276 : Litex.In _value_i16 _object_h276 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i16 _value_i16 (Litex.matrixSet (Litex.R (M := M)) _value_i14 _value_i15 (Litex.isSet (Litex.R (M := M))) h_258 h_260) _object_h276 (Litex.sameRefl _value_i16) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i14 _value_i15 (Litex.isSet (Litex.R (M := M))) h_258 h_260))) h_275)
        )
    )
  let _object_h286 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.R (M := M)) _value_i15 (Litex.isSet (Litex.R (M := M))) h_260)))
  have h_286 : Litex.In _value_i17 _object_h286 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i17 _value_i17 (Litex.finiteSeq (Litex.R (M := M)) _value_i15 (Litex.isSet (Litex.R (M := M))) h_260) _object_h286 (Litex.sameRefl _value_i17) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) _value_i15 (Litex.isSet (Litex.R (M := M))) h_260)) h_285)
        )
    )
  let _object_w50 := (Litex.matrixApply _value_i16 _value_i17 _value_i14 _value_i15 h_258 h_260 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i14 _value_i15 (Litex.isSet (Litex.C (M := M))) h_258 h_260)
    exact (show Litex.In _value_i16 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i25 : M.Value) (_raw_i26 : M.Value), M.mem _raw_i25 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i14 h_258))) → M.mem _raw_i26 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260))) → ((fun (_raw_i25 : M.Value) (_raw_i26 : M.Value) => True) _raw_i25 _raw_i26) → True := (by
          intro _raw_i25 _raw_i26 h_545 h_550 _
          let _value_i25 := Litex.semanticObject (M := M) _raw_i25 (M.member_isSet h_545)
          have h_545 : Litex.In _value_i25 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i14 h_258)) := h_545
          have h_546 : Litex.In _value_i25 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i14 h_258)) _value_i25 h_545).1
                )
            )
          have h_547 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i25 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i14 h_258)) _value_i25 h_545).2.1
                )
            )
          have h_548 : Litex.Le _value_i25 _value_i14 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i14 h_258)) _value_i25 h_545).2.2
                )
            )
          have h_549 : Litex.In _value_i25 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i14 h_258)) _value_i25 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_545)
                )
            )
          let _value_i26 := Litex.semanticObject (M := M) _raw_i26 (M.member_isSet h_550)
          have h_550 : Litex.In _value_i26 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) := h_550
          have h_551 : Litex.In _value_i26 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i26 h_550).1
                )
            )
          have h_552 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i26 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i26 h_550).2.1
                )
            )
          have h_553 : Litex.Le _value_i26 _value_i15 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i26 h_550).2.2
                )
            )
          have h_554 : Litex.In _value_i26 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i26 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_550)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i14 h_258))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i14 h_258))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i14 h_258)))
        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i25 : M.Value) (_raw_i26 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
      exact (Litex.inOfSame _value_i16 _value_i16 _object_h276 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h276
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_276))))) (by
    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i15 (Litex.isSet (Litex.C (M := M))) h_260)
    exact (by
      let _membership_function := _value_i17
      let _membership_target := (let _checked_header : ∀ (_raw_i28 : M.Value), M.mem _raw_i28 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260))) → ((fun (_raw_i28 : M.Value) => True) _raw_i28) → True := (by
          intro _raw_i28 h_647 _
          let _value_i28 := Litex.semanticObject (M := M) _raw_i28 (M.member_isSet h_647)
          have h_647 : Litex.In _value_i28 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) := h_647
          have h_648 : Litex.In _value_i28 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i28 h_647).1
                )
            )
          have h_649 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i28 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i28 h_647).2.1
                )
            )
          have h_650 : Litex.Le _value_i28 _value_i15 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i28 h_647).2.2
                )
            )
          have h_651 : Litex.In _value_i28 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i28 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_647)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i28 : M.Value) => True) _litex_input)))
      have h_652 : ∀ {_Host_i28 : Type _} [_rep_i28 : Litex.Representation M _Host_i28] (_value_i28 : Litex.Obj (M := M) _Host_i28) (h_941 : Litex.In _value_i28 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260))), (by
        let _object_w39 := (let _litex_call_arg_0 := _value_i28;
        Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i20 : M.Value) => True) _litex_input) _value_i17 _litex_call_arg_0 h_286 (by
          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260))
          exact h_941) True.intro)
        exact (by
          let _atomic_wd_2_0 := _object_w39
          exact Litex.In _atomic_wd_2_0 (Litex.C (M := M)))
      ) := (by
        intro _Host_i28 _rep_i28 _value_i28 h_941
        have h_942 : Litex.In _value_i28 (Litex.Z (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i28 h_941).1
              )
          )
        have h_943 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i28 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i28 h_941).2.1
              )
          )
        have h_944 : Litex.Le _value_i28 _value_i15 :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i28 h_941).2.2
              )
          )
        have h_945 : Litex.In _value_i28 (Litex.NPos (M := M)) :=
          (by
            litex_checked_step =>
              exact (
                (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i28 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_941)
              )
          )
        let _object_w39 := (let _litex_call_arg_0 := _value_i28;
        Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i20 : M.Value) => True) _litex_input) _value_i17 _litex_call_arg_0 h_286 (by
          let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260))
          exact h_941) True.intro)
        have h_653 : (by
          let _atomic_wd_2_0 := _object_w39
          exact Litex.In _atomic_wd_2_0 (Litex.C (M := M))) :=
          (by
            litex_checked_step =>
              exact (
                (by
                  let _atomic_wd_2_0 := _object_w39
                  exact (Litex.realToComplex _atomic_wd_2_0 (Litex.callOnInOutput _atomic_wd_2_0)))
              )
          )
        exact h_653
      )
      exact (by
        let _source_signature := (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i29 : M.Value) => True) _litex_input))
        have _source_member : Litex.In _membership_function (Litex.fnSet _source_signature) := (Litex.inOfSame _value_i17 _value_i17 (Litex.finiteSeq (Litex.R (M := M)) _value_i15 (Litex.isSet (Litex.R (M := M))) h_260) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i29 : M.Value) => True) _litex_input))) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) _value_i15 (Litex.isSet (Litex.R (M := M))) h_260))) h_285)
        have _same_domain : _source_signature.domain = _membership_target.val.domain := (by rfl)
        change M.mem (Litex.denote _membership_function) (Litex.FunctionSemantics.fnSetValue _membership_target.val.domain _membership_target.val.output)
        have _source_graph : M.mem (Litex.denote _membership_function) (Litex.FunctionSemantics.fnSetValue _source_signature.domain _source_signature.output) := _source_member
        rw [_same_domain] at _source_graph
        apply Litex.FunctionSemantics.fnSet_of_returns _source_graph
        intro _input _hin
        change M.mem _input (Litex.SetSemantics.sepValue _ _) at _hin
        obtain ⟨_members, _guard⟩ := (Litex.SetSemantics.sep_members _ _ _).mp _hin
        let _raw_0 := _input
        have _member_0 := _members
        let _arg_0 := Litex.semanticObject (M := M) _raw_0 (M.member_isSet _member_0)
        exact h_652 _arg_0 _member_0))))
  let _object_w51 := (Litex.finiteSeq (Litex.R (M := M)) _value_i14 (Litex.isSet (Litex.R (M := M))) h_258)
  exact (by
    let _atomic_wd_1_0 := _object_w50
    let _atomic_wd_1_1 := _object_w51
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i14 _rep_i14 _value_i14 h_258 _Host_i15 _rep_i15 _value_i15 h_260 _Host_i16 _rep_i16 _value_i16 h_275 _Host_i17 _rep_i17 _value_i17 h_285
          have h_259 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i14 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i14 h_258)
                )
            )
          have h_261 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i15 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i15 h_260)
                )
            )
          let _object_h276 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i14 _value_i15 (Litex.isSet (Litex.R (M := M))) h_258 h_260)))
          have h_276 : Litex.In _value_i16 _object_h276 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i16 _value_i16 (Litex.matrixSet (Litex.R (M := M)) _value_i14 _value_i15 (Litex.isSet (Litex.R (M := M))) h_258 h_260) _object_h276 (Litex.sameRefl _value_i16) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i14 _value_i15 (Litex.isSet (Litex.R (M := M))) h_258 h_260))) h_275)
                )
            )
          let _object_h286 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.R (M := M)) _value_i15 (Litex.isSet (Litex.R (M := M))) h_260)))
          have h_286 : Litex.In _value_i17 _object_h286 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i17 _value_i17 (Litex.finiteSeq (Litex.R (M := M)) _value_i15 (Litex.isSet (Litex.R (M := M))) h_260) _object_h286 (Litex.sameRefl _value_i17) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) _value_i15 (Litex.isSet (Litex.R (M := M))) h_260)) h_285)
                )
            )
          let _object_w50 := (Litex.matrixApply _value_i16 _value_i17 _value_i14 _value_i15 h_258 h_260 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i14 _value_i15 (Litex.isSet (Litex.C (M := M))) h_258 h_260)
            exact (show Litex.In _value_i16 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
              let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i25 : M.Value) (_raw_i26 : M.Value), M.mem _raw_i25 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i14 h_258))) → M.mem _raw_i26 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260))) → ((fun (_raw_i25 : M.Value) (_raw_i26 : M.Value) => True) _raw_i25 _raw_i26) → True := (by
                  intro _raw_i25 _raw_i26 h_545 h_550 _
                  let _value_i25 := Litex.semanticObject (M := M) _raw_i25 (M.member_isSet h_545)
                  have h_545 : Litex.In _value_i25 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i14 h_258)) := h_545
                  have h_546 : Litex.In _value_i25 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i14 h_258)) _value_i25 h_545).1
                        )
                    )
                  have h_547 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i25 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i14 h_258)) _value_i25 h_545).2.1
                        )
                    )
                  have h_548 : Litex.Le _value_i25 _value_i14 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i14 h_258)) _value_i25 h_545).2.2
                        )
                    )
                  have h_549 : Litex.In _value_i25 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i14 h_258)) _value_i25 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_545)
                        )
                    )
                  let _value_i26 := Litex.semanticObject (M := M) _raw_i26 (M.member_isSet h_550)
                  have h_550 : Litex.In _value_i26 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) := h_550
                  have h_551 : Litex.In _value_i26 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i26 h_550).1
                        )
                    )
                  have h_552 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i26 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i26 h_550).2.1
                        )
                    )
                  have h_553 : Litex.Le _value_i26 _value_i15 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i26 h_550).2.2
                        )
                    )
                  have h_554 : Litex.In _value_i26 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i26 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_550)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i14 h_258))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i14 h_258))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)))] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i14 h_258)))
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i25 : M.Value) (_raw_i26 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
              exact (Litex.inOfSame _value_i16 _value_i16 _object_h276 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h276
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                exact (show Litex.Same _left _right from rfl)) h_276))))) (by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.C (M := M)) _value_i15 (Litex.isSet (Litex.C (M := M))) h_260)
            exact (by
              let _membership_function := _value_i17
              let _membership_target := (let _checked_header : ∀ (_raw_i28 : M.Value), M.mem _raw_i28 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260))) → ((fun (_raw_i28 : M.Value) => True) _raw_i28) → True := (by
                  intro _raw_i28 h_647 _
                  let _value_i28 := Litex.semanticObject (M := M) _raw_i28 (M.member_isSet h_647)
                  have h_647 : Litex.In _value_i28 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) := h_647
                  have h_648 : Litex.In _value_i28 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i28 h_647).1
                        )
                    )
                  have h_649 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i28 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i28 h_647).2.1
                        )
                    )
                  have h_650 : Litex.Le _value_i28 _value_i15 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i28 h_647).2.2
                        )
                    )
                  have h_651 : Litex.In _value_i28 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i28 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_647)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.C (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i28 : M.Value) => True) _litex_input)))
              have h_652 : ∀ {_Host_i28 : Type _} [_rep_i28 : Litex.Representation M _Host_i28] (_value_i28 : Litex.Obj (M := M) _Host_i28) (h_941 : Litex.In _value_i28 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260))), (by
                let _object_w39 := (let _litex_call_arg_0 := _value_i28;
                Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i20 : M.Value) => True) _litex_input) _value_i17 _litex_call_arg_0 h_286 (by
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260))
                  exact h_941) True.intro)
                exact (by
                  let _atomic_wd_2_0 := _object_w39
                  exact Litex.In _atomic_wd_2_0 (Litex.C (M := M)))
              ) := (by
                intro _Host_i28 _rep_i28 _value_i28 h_941
                have h_942 : Litex.In _value_i28 (Litex.Z (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i28 h_941).1
                      )
                  )
                have h_943 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i28 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i28 h_941).2.1
                      )
                  )
                have h_944 : Litex.Le _value_i28 _value_i15 :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i28 h_941).2.2
                      )
                  )
                have h_945 : Litex.In _value_i28 (Litex.NPos (M := M)) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i28 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_941)
                      )
                  )
                let _object_w39 := (let _litex_call_arg_0 := _value_i28;
                Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i20 : M.Value) => True) _litex_input) _value_i17 _litex_call_arg_0 h_286 (by
                  let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260))
                  exact h_941) True.intro)
                have h_653 : (by
                  let _atomic_wd_2_0 := _object_w39
                  exact Litex.In _atomic_wd_2_0 (Litex.C (M := M))) :=
                  (by
                    litex_checked_step =>
                      exact (
                        (by
                          let _atomic_wd_2_0 := _object_w39
                          exact (Litex.realToComplex _atomic_wd_2_0 (Litex.callOnInOutput _atomic_wd_2_0)))
                      )
                  )
                exact h_653
              )
              exact (by
                let _source_signature := (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i29 : M.Value) => True) _litex_input))
                have _source_member : Litex.In _membership_function (Litex.fnSet _source_signature) := (Litex.inOfSame _value_i17 _value_i17 (Litex.finiteSeq (Litex.R (M := M)) _value_i15 (Litex.isSet (Litex.R (M := M))) h_260) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i29 : M.Value) => True) _litex_input))) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) _value_i15 (Litex.isSet (Litex.R (M := M))) h_260))) h_285)
                have _same_domain : _source_signature.domain = _membership_target.val.domain := (by rfl)
                change M.mem (Litex.denote _membership_function) (Litex.FunctionSemantics.fnSetValue _membership_target.val.domain _membership_target.val.output)
                have _source_graph : M.mem (Litex.denote _membership_function) (Litex.FunctionSemantics.fnSetValue _source_signature.domain _source_signature.output) := _source_member
                rw [_same_domain] at _source_graph
                apply Litex.FunctionSemantics.fnSet_of_returns _source_graph
                intro _input _hin
                change M.mem _input (Litex.SetSemantics.sepValue _ _) at _hin
                obtain ⟨_members, _guard⟩ := (Litex.SetSemantics.sep_members _ _ _).mp _hin
                let _raw_0 := _input
                have _member_0 := _members
                let _arg_0 := Litex.semanticObject (M := M) _raw_0 (M.member_isSet _member_0)
                exact h_652 _arg_0 _member_0))))
          let _object_w51 := (Litex.finiteSeq (Litex.R (M := M)) _value_i14 (Litex.isSet (Litex.R (M := M))) h_258)
          have h_237 : (by
            let _atomic_wd_1_0 := _object_w50
            let _atomic_wd_1_1 := _object_w51
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w50
                    let _atomic_wd_1_1 := _object_w51
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixApplySignature (_litex_matrix).val.rows .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixApplyInRealFnSet _litex_matrix (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i31 : M.Value) (_raw_i32 : M.Value), M.mem _raw_i31 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i14 h_258))) → M.mem _raw_i32 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260))) → ((fun (_raw_i31 : M.Value) (_raw_i32 : M.Value) => True) _raw_i31 _raw_i32) → True := (by
                          intro _raw_i31 _raw_i32 h_1254 h_1259 _
                          let _value_i31 := Litex.semanticObject (M := M) _raw_i31 (M.member_isSet h_1254)
                          have h_1254 : Litex.In _value_i31 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i14 h_258)) := h_1254
                          have h_1255 : Litex.In _value_i31 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i14 h_258)) _value_i31 h_1254).1
                                )
                            )
                          have h_1256 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i31 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i14 h_258)) _value_i31 h_1254).2.1
                                )
                            )
                          have h_1257 : Litex.Le _value_i31 _value_i14 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i14 h_258)) _value_i31 h_1254).2.2
                                )
                            )
                          have h_1258 : Litex.In _value_i31 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i14 h_258)) _value_i31 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1254)
                                )
                            )
                          let _value_i32 := Litex.semanticObject (M := M) _raw_i32 (M.member_isSet h_1259)
                          have h_1259 : Litex.In _value_i32 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) := h_1259
                          have h_1260 : Litex.In _value_i32 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i32 h_1259).1
                                )
                            )
                          have h_1261 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i32 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i32 h_1259).2.1
                                )
                            )
                          have h_1262 : Litex.Le _value_i32 _value_i15 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i32 h_1259).2.2
                                )
                            )
                          have h_1263 : Litex.In _value_i32 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i32 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1259)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i14 h_258))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i14 h_258))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i14 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i14 h_258)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i31 : M.Value) (_raw_i32 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                      exact (Litex.inOfSame _value_i16 _value_i16 _object_h276 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h276
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_276)) (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i33 : M.Value), M.mem _raw_i33 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260))) → ((fun (_raw_i33 : M.Value) => True) _raw_i33) → True := (by
                          intro _raw_i33 h_1316 _
                          let _value_i33 := Litex.semanticObject (M := M) _raw_i33 (M.member_isSet h_1316)
                          have h_1316 : Litex.In _value_i33 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) := h_1316
                          have h_1317 : Litex.In _value_i33 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i33 h_1316).1
                                )
                            )
                          have h_1318 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i33 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i33 h_1316).2.1
                                )
                            )
                          have h_1319 : Litex.Le _value_i33 _value_i15 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i33 h_1316).2.2
                                )
                            )
                          have h_1320 : Litex.In _value_i33 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260)) _value_i33 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1316)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260))) (Litex.denote _litex_output) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_260))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i33 : M.Value) => True) _litex_input)))
                      exact (Litex.inOfSame _value_i17 _value_i17 _object_h286 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h286
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_286))))))
                )
            )
          let _object_h1337 := (Litex.fnSet (Litex.finiteSeqSignature _object_w51))
          have h_1337 : Litex.In _object_w50 _object_h1337 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _object_w50 _object_w50 _object_w51 _object_h1337 (Litex.sameRefl _object_w50) (Litex.finiteSeq_eq_fnSet _object_w51) h_237)
                )
            )
          exact h_237
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_vector_x5f_application_x2f_statement_x2e_lit
