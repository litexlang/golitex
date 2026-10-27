import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_multiplication_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v21 v22 v23 v24 v25
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_23 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_25 : Litex.In _value_i2 (Litex.N (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_27 : Litex.In _value_i3 (Litex.N (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_42 : Litex.In _value_i4 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_23 h_25)) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_61 : Litex.In _value_i5 (Litex.matrixSet (Litex.C (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.C (M := M))) h_25 h_27)), (by
  let _object_w12 := (Litex.matrixMultiply _value_i4 _value_i5 _value_i1 _value_i2 _value_i3 h_23 h_25 h_27 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_23 h_25)
    exact h_42) (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.C (M := M))) h_25 h_27)
    exact h_61))
  let _object_w13 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i3 (Litex.isSet (Litex.C (M := M))) h_23 h_27)
  exact (by
    let _atomic_wd_1_0 := _object_w12
    let _atomic_wd_1_1 := _object_w13
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_23 _Host_i2 _rep_i2 _value_i2 h_25 _Host_i3 _rep_i3 _value_i3 h_27 _Host_i4 _rep_i4 _value_i4 h_42 _Host_i5 _rep_i5 _value_i5 h_61
          have h_24 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_23)
                )
            )
          have h_26 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_25)
                )
            )
          have h_28 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i3 h_27)
                )
            )
          let _object_h43 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_23 h_25)))
          have h_43 : Litex.In _value_i4 _object_h43 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i4 _value_i4 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_23 h_25) _object_h43 (Litex.sameRefl _value_i4) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_23 h_25))) h_42)
                )
            )
          let _object_h62 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.C (M := M))) h_25 h_27)))
          have h_62 : Litex.In _value_i5 _object_h62 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i5 _value_i5 (Litex.matrixSet (Litex.C (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.C (M := M))) h_25 h_27) _object_h62 (Litex.sameRefl _value_i5) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.C (M := M))) h_25 h_27))) h_61)
                )
            )
          let _object_w12 := (Litex.matrixMultiply _value_i4 _value_i5 _value_i1 _value_i2 _value_i3 h_23 h_25 h_27 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_23 h_25)
            exact h_42) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i2 _value_i3 (Litex.isSet (Litex.C (M := M))) h_25 h_27)
            exact h_61))
          let _object_w13 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i3 (Litex.isSet (Litex.C (M := M))) h_23 h_27)
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
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixMultiplyInFnSet _litex_matrix))))
                )
            )
          let _object_h288 := (Litex.fnSet (Litex.matrixSignature _object_w13))
          have h_288 : Litex.In _object_w12 _object_h288 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _object_w12 _object_w12 _object_w13 _object_h288 (Litex.sameRefl _object_w12) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet _object_w13)) h_1)
                )
            )
          exact h_1
        )
      )
  )

theorem h_290 : ∀ {_Host_i21 : Type v21} [_rep_i21 : Litex.Representation M _Host_i21] (_value_i21 : Litex.Obj (M := M) _Host_i21) (h_311 : Litex.In _value_i21 (Litex.N (M := M))) {_Host_i22 : Type v22} [_rep_i22 : Litex.Representation M _Host_i22] (_value_i22 : Litex.Obj (M := M) _Host_i22) (h_313 : Litex.In _value_i22 (Litex.N (M := M))) {_Host_i23 : Type v23} [_rep_i23 : Litex.Representation M _Host_i23] (_value_i23 : Litex.Obj (M := M) _Host_i23) (h_315 : Litex.In _value_i23 (Litex.N (M := M))) {_Host_i24 : Type v24} [_rep_i24 : Litex.Representation M _Host_i24] (_value_i24 : Litex.Obj (M := M) _Host_i24) (h_330 : Litex.In _value_i24 (Litex.matrixSet (Litex.R (M := M)) _value_i21 _value_i22 (Litex.isSet (Litex.R (M := M))) h_311 h_313)) {_Host_i25 : Type v25} [_rep_i25 : Litex.Representation M _Host_i25] (_value_i25 : Litex.Obj (M := M) _Host_i25) (h_349 : Litex.In _value_i25 (Litex.matrixSet (Litex.R (M := M)) _value_i22 _value_i23 (Litex.isSet (Litex.R (M := M))) h_313 h_315)), (by
  let _object_h331 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i21 _value_i22 (Litex.isSet (Litex.R (M := M))) h_311 h_313)))
  have h_331 : Litex.In _value_i24 _object_h331 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i24 _value_i24 (Litex.matrixSet (Litex.R (M := M)) _value_i21 _value_i22 (Litex.isSet (Litex.R (M := M))) h_311 h_313) _object_h331 (Litex.sameRefl _value_i24) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i21 _value_i22 (Litex.isSet (Litex.R (M := M))) h_311 h_313))) h_330)
        )
    )
  let _object_h350 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i22 _value_i23 (Litex.isSet (Litex.R (M := M))) h_313 h_315)))
  have h_350 : Litex.In _value_i25 _object_h350 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i25 _value_i25 (Litex.matrixSet (Litex.R (M := M)) _value_i22 _value_i23 (Litex.isSet (Litex.R (M := M))) h_313 h_315) _object_h350 (Litex.sameRefl _value_i25) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i22 _value_i23 (Litex.isSet (Litex.R (M := M))) h_313 h_315))) h_349)
        )
    )
  let _object_w51 := (Litex.matrixMultiply _value_i24 _value_i25 _value_i21 _value_i22 _value_i23 h_311 h_313 h_315 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i21 _value_i22 (Litex.isSet (Litex.C (M := M))) h_311 h_313)
    exact (show Litex.In _value_i24 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i34 : M.Value) (_raw_i35 : M.Value), M.mem _raw_i34 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i21 h_311))) → M.mem _raw_i35 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313))) → ((fun (_raw_i34 : M.Value) (_raw_i35 : M.Value) => True) _raw_i34 _raw_i35) → True := (by
          intro _raw_i34 _raw_i35 h_646 h_651 _
          let _value_i34 := Litex.semanticObject (M := M) _raw_i34 (M.member_isSet h_646)
          have h_646 : Litex.In _value_i34 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i21 h_311)) := h_646
          have h_647 : Litex.In _value_i34 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i21 h_311)) _value_i34 h_646).1
                )
            )
          have h_648 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i34 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i21 h_311)) _value_i34 h_646).2.1
                )
            )
          have h_649 : Litex.Le _value_i34 _value_i21 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i21 h_311)) _value_i34 h_646).2.2
                )
            )
          have h_650 : Litex.In _value_i34 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i21 h_311)) _value_i34 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_646)
                )
            )
          let _value_i35 := Litex.semanticObject (M := M) _raw_i35 (M.member_isSet h_651)
          have h_651 : Litex.In _value_i35 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) := h_651
          have h_652 : Litex.In _value_i35 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) _value_i35 h_651).1
                )
            )
          have h_653 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i35 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) _value_i35 h_651).2.1
                )
            )
          have h_654 : Litex.Le _value_i35 _value_i22 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) _value_i35 h_651).2.2
                )
            )
          have h_655 : Litex.In _value_i35 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) _value_i35 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_651)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i21 h_311))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i21 h_311))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i21 h_311)))
        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i34 : M.Value) (_raw_i35 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
      exact (Litex.inOfSame _value_i24 _value_i24 _object_h331 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h331
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_331))))) (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i22 _value_i23 (Litex.isSet (Litex.C (M := M))) h_313 h_315)
    exact (show Litex.In _value_i25 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i40 : M.Value) (_raw_i41 : M.Value), M.mem _raw_i40 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313))) → M.mem _raw_i41 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_315))) → ((fun (_raw_i40 : M.Value) (_raw_i41 : M.Value) => True) _raw_i40 _raw_i41) → True := (by
          intro _raw_i40 _raw_i41 h_952 h_957 _
          let _value_i40 := Litex.semanticObject (M := M) _raw_i40 (M.member_isSet h_952)
          have h_952 : Litex.In _value_i40 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) := h_952
          have h_953 : Litex.In _value_i40 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) _value_i40 h_952).1
                )
            )
          have h_954 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i40 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) _value_i40 h_952).2.1
                )
            )
          have h_955 : Litex.Le _value_i40 _value_i22 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) _value_i40 h_952).2.2
                )
            )
          have h_956 : Litex.In _value_i40 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) _value_i40 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_952)
                )
            )
          let _value_i41 := Litex.semanticObject (M := M) _raw_i41 (M.member_isSet h_957)
          have h_957 : Litex.In _value_i41 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_315)) := h_957
          have h_958 : Litex.In _value_i41 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_315)) _value_i41 h_957).1
                )
            )
          have h_959 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i41 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_315)) _value_i41 h_957).2.1
                )
            )
          have h_960 : Litex.Le _value_i41 _value_i23 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_315)) _value_i41 h_957).2.2
                )
            )
          have h_961 : Litex.In _value_i41 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_315)) _value_i41 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_957)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_315)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_315)))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)))
        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_315)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i40 : M.Value) (_raw_i41 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
      exact (Litex.inOfSame _value_i25 _value_i25 _object_h350 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h350
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_350))))))
  let _object_w52 := (Litex.matrixSet (Litex.R (M := M)) _value_i21 _value_i23 (Litex.isSet (Litex.R (M := M))) h_311 h_315)
  exact (by
    let _atomic_wd_1_0 := _object_w51
    let _atomic_wd_1_1 := _object_w52
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i21 _rep_i21 _value_i21 h_311 _Host_i22 _rep_i22 _value_i22 h_313 _Host_i23 _rep_i23 _value_i23 h_315 _Host_i24 _rep_i24 _value_i24 h_330 _Host_i25 _rep_i25 _value_i25 h_349
          have h_312 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i21 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i21 h_311)
                )
            )
          have h_314 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i22 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i22 h_313)
                )
            )
          have h_316 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i23 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i23 h_315)
                )
            )
          let _object_h331 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i21 _value_i22 (Litex.isSet (Litex.R (M := M))) h_311 h_313)))
          have h_331 : Litex.In _value_i24 _object_h331 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i24 _value_i24 (Litex.matrixSet (Litex.R (M := M)) _value_i21 _value_i22 (Litex.isSet (Litex.R (M := M))) h_311 h_313) _object_h331 (Litex.sameRefl _value_i24) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i21 _value_i22 (Litex.isSet (Litex.R (M := M))) h_311 h_313))) h_330)
                )
            )
          let _object_h350 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i22 _value_i23 (Litex.isSet (Litex.R (M := M))) h_313 h_315)))
          have h_350 : Litex.In _value_i25 _object_h350 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i25 _value_i25 (Litex.matrixSet (Litex.R (M := M)) _value_i22 _value_i23 (Litex.isSet (Litex.R (M := M))) h_313 h_315) _object_h350 (Litex.sameRefl _value_i25) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i22 _value_i23 (Litex.isSet (Litex.R (M := M))) h_313 h_315))) h_349)
                )
            )
          let _object_w51 := (Litex.matrixMultiply _value_i24 _value_i25 _value_i21 _value_i22 _value_i23 h_311 h_313 h_315 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i21 _value_i22 (Litex.isSet (Litex.C (M := M))) h_311 h_313)
            exact (show Litex.In _value_i24 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
              let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i34 : M.Value) (_raw_i35 : M.Value), M.mem _raw_i34 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i21 h_311))) → M.mem _raw_i35 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313))) → ((fun (_raw_i34 : M.Value) (_raw_i35 : M.Value) => True) _raw_i34 _raw_i35) → True := (by
                  intro _raw_i34 _raw_i35 h_646 h_651 _
                  let _value_i34 := Litex.semanticObject (M := M) _raw_i34 (M.member_isSet h_646)
                  have h_646 : Litex.In _value_i34 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i21 h_311)) := h_646
                  have h_647 : Litex.In _value_i34 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i21 h_311)) _value_i34 h_646).1
                        )
                    )
                  have h_648 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i34 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i21 h_311)) _value_i34 h_646).2.1
                        )
                    )
                  have h_649 : Litex.Le _value_i34 _value_i21 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i21 h_311)) _value_i34 h_646).2.2
                        )
                    )
                  have h_650 : Litex.In _value_i34 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i21 h_311)) _value_i34 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_646)
                        )
                    )
                  let _value_i35 := Litex.semanticObject (M := M) _raw_i35 (M.member_isSet h_651)
                  have h_651 : Litex.In _value_i35 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) := h_651
                  have h_652 : Litex.In _value_i35 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) _value_i35 h_651).1
                        )
                    )
                  have h_653 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i35 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) _value_i35 h_651).2.1
                        )
                    )
                  have h_654 : Litex.Le _value_i35 _value_i22 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) _value_i35 h_651).2.2
                        )
                    )
                  have h_655 : Litex.In _value_i35 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) _value_i35 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_651)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i21 h_311))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i21 h_311))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)))] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i21 h_311)))
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i34 : M.Value) (_raw_i35 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
              exact (Litex.inOfSame _value_i24 _value_i24 _object_h331 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h331
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                exact (show Litex.Same _left _right from rfl)) h_331))))) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i22 _value_i23 (Litex.isSet (Litex.C (M := M))) h_313 h_315)
            exact (show Litex.In _value_i25 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
              let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i40 : M.Value) (_raw_i41 : M.Value), M.mem _raw_i40 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313))) → M.mem _raw_i41 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_315))) → ((fun (_raw_i40 : M.Value) (_raw_i41 : M.Value) => True) _raw_i40 _raw_i41) → True := (by
                  intro _raw_i40 _raw_i41 h_952 h_957 _
                  let _value_i40 := Litex.semanticObject (M := M) _raw_i40 (M.member_isSet h_952)
                  have h_952 : Litex.In _value_i40 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) := h_952
                  have h_953 : Litex.In _value_i40 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) _value_i40 h_952).1
                        )
                    )
                  have h_954 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i40 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) _value_i40 h_952).2.1
                        )
                    )
                  have h_955 : Litex.Le _value_i40 _value_i22 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) _value_i40 h_952).2.2
                        )
                    )
                  have h_956 : Litex.In _value_i40 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) _value_i40 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_952)
                        )
                    )
                  let _value_i41 := Litex.semanticObject (M := M) _raw_i41 (M.member_isSet h_957)
                  have h_957 : Litex.In _value_i41 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_315)) := h_957
                  have h_958 : Litex.In _value_i41 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_315)) _value_i41 h_957).1
                        )
                    )
                  have h_959 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i41 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_315)) _value_i41 h_957).2.1
                        )
                    )
                  have h_960 : Litex.Le _value_i41 _value_i23 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_315)) _value_i41 h_957).2.2
                        )
                    )
                  have h_961 : Litex.In _value_i41 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_315)) _value_i41 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_957)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_315)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_315)))] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)))
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_315)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i40 : M.Value) (_raw_i41 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
              exact (Litex.inOfSame _value_i25 _value_i25 _object_h350 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h350
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                exact (show Litex.Same _left _right from rfl)) h_350))))))
          let _object_w52 := (Litex.matrixSet (Litex.R (M := M)) _value_i21 _value_i23 (Litex.isSet (Litex.R (M := M))) h_311 h_315)
          have h_289 : (by
            let _atomic_wd_1_0 := _object_w51
            let _atomic_wd_1_1 := _object_w52
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w51
                    let _atomic_wd_1_1 := _object_w52
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixMultiplyInRealFnSet _litex_matrix (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i46 : M.Value) (_raw_i47 : M.Value), M.mem _raw_i46 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i21 h_311))) → M.mem _raw_i47 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313))) → ((fun (_raw_i46 : M.Value) (_raw_i47 : M.Value) => True) _raw_i46 _raw_i47) → True := (by
                          intro _raw_i46 _raw_i47 h_1111 h_1116 _
                          let _value_i46 := Litex.semanticObject (M := M) _raw_i46 (M.member_isSet h_1111)
                          have h_1111 : Litex.In _value_i46 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i21 h_311)) := h_1111
                          have h_1112 : Litex.In _value_i46 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i21 h_311)) _value_i46 h_1111).1
                                )
                            )
                          have h_1113 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i46 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i21 h_311)) _value_i46 h_1111).2.1
                                )
                            )
                          have h_1114 : Litex.Le _value_i46 _value_i21 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i21 h_311)) _value_i46 h_1111).2.2
                                )
                            )
                          have h_1115 : Litex.In _value_i46 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i21 h_311)) _value_i46 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1111)
                                )
                            )
                          let _value_i47 := Litex.semanticObject (M := M) _raw_i47 (M.member_isSet h_1116)
                          have h_1116 : Litex.In _value_i47 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) := h_1116
                          have h_1117 : Litex.In _value_i47 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) _value_i47 h_1116).1
                                )
                            )
                          have h_1118 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i47 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) _value_i47 h_1116).2.1
                                )
                            )
                          have h_1119 : Litex.Le _value_i47 _value_i22 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) _value_i47 h_1116).2.2
                                )
                            )
                          have h_1120 : Litex.In _value_i47 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) _value_i47 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1116)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i21 h_311))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i21 h_311))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i21 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i21 h_311)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i46 : M.Value) (_raw_i47 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                      exact (Litex.inOfSame _value_i24 _value_i24 _object_h331 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h331
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_331)) (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i48 : M.Value) (_raw_i49 : M.Value), M.mem _raw_i48 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313))) → M.mem _raw_i49 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_315))) → ((fun (_raw_i48 : M.Value) (_raw_i49 : M.Value) => True) _raw_i48 _raw_i49) → True := (by
                          intro _raw_i48 _raw_i49 h_1225 h_1230 _
                          let _value_i48 := Litex.semanticObject (M := M) _raw_i48 (M.member_isSet h_1225)
                          have h_1225 : Litex.In _value_i48 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) := h_1225
                          have h_1226 : Litex.In _value_i48 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) _value_i48 h_1225).1
                                )
                            )
                          have h_1227 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i48 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) _value_i48 h_1225).2.1
                                )
                            )
                          have h_1228 : Litex.Le _value_i48 _value_i22 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) _value_i48 h_1225).2.2
                                )
                            )
                          have h_1229 : Litex.In _value_i48 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)) _value_i48 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1225)
                                )
                            )
                          let _value_i49 := Litex.semanticObject (M := M) _raw_i49 (M.member_isSet h_1230)
                          have h_1230 : Litex.In _value_i49 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_315)) := h_1230
                          have h_1231 : Litex.In _value_i49 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_315)) _value_i49 h_1230).1
                                )
                            )
                          have h_1232 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i49 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_315)) _value_i49 h_1230).2.1
                                )
                            )
                          have h_1233 : Litex.Le _value_i49 _value_i23 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_315)) _value_i49 h_1230).2.2
                                )
                            )
                          have h_1234 : Litex.In _value_i49 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_315)) _value_i49 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_1230)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_315)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_315)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i22 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i22 h_313)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i23 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i23 h_315)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i48 : M.Value) (_raw_i49 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                      exact (Litex.inOfSame _value_i25 _value_i25 _object_h350 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h350
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_350))))))
                )
            )
          let _object_h1253 := (Litex.fnSet (Litex.matrixSignature _object_w52))
          have h_1253 : Litex.In _object_w51 _object_h1253 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _object_w51 _object_w51 _object_w52 _object_h1253 (Litex.sameRefl _object_w51) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet _object_w52)) h_289)
                )
            )
          exact h_289
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_multiplication_x2f_statement_x2e_lit
