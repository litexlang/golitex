import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_scale_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v17 v18 v19 v20
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_31 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_33 : Litex.In _value_i2 (Litex.N (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_35 : Litex.In _value_i3 (Litex.C (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_49 : Litex.In _value_i4 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_31 h_33)), (by
  let _object_w11 := (Litex.matrixScale _value_i3 _value_i4 _value_i1 _value_i2 h_35 h_31 h_33 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_31 h_33)
    exact h_49))
  exact (by
    let _atomic_wd_1_0 := _object_w11
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_31 h_33)
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_31 _Host_i2 _rep_i2 _value_i2 h_33 _Host_i3 _rep_i3 _value_i3 h_35 _Host_i4 _rep_i4 _value_i4 h_49
          have h_32 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_31)
                )
            )
          have h_34 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_33)
                )
            )
          let _object_h50 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_31 h_33)))
          have h_50 : Litex.In _value_i4 _object_h50 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i4 _value_i4 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_31 h_33) _object_h50 (Litex.sameRefl _value_i4) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_31 h_33))) h_49)
                )
            )
          let _object_w11 := (Litex.matrixScale _value_i3 _value_i4 _value_i1 _value_i2 h_35 h_31 h_33 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_31 h_33)
            exact h_49))
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w11
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_31 h_33)
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w11
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_31 h_33)
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixScaleInFnSet _litex_matrix))))
                )
            )
          let _object_h210 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_31 h_33)))
          have h_210 : Litex.In _object_w11 _object_h210 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _object_w11 _object_w11 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_31 h_33) _object_h210 (Litex.sameRefl _object_w11) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i2 (Litex.isSet (Litex.C (M := M))) h_31 h_33))) h_1)
                )
            )
          exact h_1
        )
      )
  )

theorem h_212 : ∀ {_Host_i17 : Type v17} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_241 : Litex.In _value_i17 (Litex.N (M := M))) {_Host_i18 : Type v18} [_rep_i18 : Litex.Representation M _Host_i18] (_value_i18 : Litex.Obj (M := M) _Host_i18) (h_243 : Litex.In _value_i18 (Litex.N (M := M))) {_Host_i19 : Type v19} [_rep_i19 : Litex.Representation M _Host_i19] (_value_i19 : Litex.Obj (M := M) _Host_i19) (h_245 : Litex.In _value_i19 (Litex.R (M := M))) {_Host_i20 : Type v20} [_rep_i20 : Litex.Representation M _Host_i20] (_value_i20 : Litex.Obj (M := M) _Host_i20) (h_259 : Litex.In _value_i20 (Litex.matrixSet (Litex.R (M := M)) _value_i17 _value_i18 (Litex.isSet (Litex.R (M := M))) h_241 h_243)), (by
  let _object_h260 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i17 _value_i18 (Litex.isSet (Litex.R (M := M))) h_241 h_243)))
  have h_260 : Litex.In _value_i20 _object_h260 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i20 _value_i20 (Litex.matrixSet (Litex.R (M := M)) _value_i17 _value_i18 (Litex.isSet (Litex.R (M := M))) h_241 h_243) _object_h260 (Litex.sameRefl _value_i20) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i17 _value_i18 (Litex.isSet (Litex.R (M := M))) h_241 h_243))) h_259)
        )
    )
  let _object_w33 := (Litex.matrixScale _value_i19 _value_i20 _value_i17 _value_i18 (M.real_subset_complex _ h_245) h_241 h_243 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i17 _value_i18 (Litex.isSet (Litex.C (M := M))) h_241 h_243)
    exact (show Litex.In _value_i20 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i27 : M.Value) (_raw_i28 : M.Value), M.mem _raw_i27 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 h_241))) → M.mem _raw_i28 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i18 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i18 h_243))) → ((fun (_raw_i27 : M.Value) (_raw_i28 : M.Value) => True) _raw_i27 _raw_i28) → True := (by
          intro _raw_i27 _raw_i28 h_515 h_520 _
          let _value_i27 := Litex.semanticObject (M := M) _raw_i27 (M.member_isSet h_515)
          have h_515 : Litex.In _value_i27 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 h_241)) := h_515
          have h_516 : Litex.In _value_i27 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 h_241)) _value_i27 h_515).1
                )
            )
          have h_517 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i27 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 h_241)) _value_i27 h_515).2.1
                )
            )
          have h_518 : Litex.Le _value_i27 _value_i17 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 h_241)) _value_i27 h_515).2.2
                )
            )
          have h_519 : Litex.In _value_i27 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 h_241)) _value_i27 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_515)
                )
            )
          let _value_i28 := Litex.semanticObject (M := M) _raw_i28 (M.member_isSet h_520)
          have h_520 : Litex.In _value_i28 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i18 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i18 h_243)) := h_520
          have h_521 : Litex.In _value_i28 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i18 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i18 h_243)) _value_i28 h_520).1
                )
            )
          have h_522 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i28 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i18 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i18 h_243)) _value_i28 h_520).2.1
                )
            )
          have h_523 : Litex.Le _value_i28 _value_i18 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i18 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i18 h_243)) _value_i28 h_520).2.2
                )
            )
          have h_524 : Litex.In _value_i28 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i18 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i18 h_243)) _value_i28 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_520)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 h_241))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i18 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i18 h_243)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 h_241))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i18 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i18 h_243)))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 h_241)))
        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i18 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i18 h_243)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i27 : M.Value) (_raw_i28 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
      exact (Litex.inOfSame _value_i20 _value_i20 _object_h260 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h260
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_260))))))
  exact (by
    let _atomic_wd_1_0 := _object_w33
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.R (M := M)) _value_i17 _value_i18 (Litex.isSet (Litex.R (M := M))) h_241 h_243)
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i17 _rep_i17 _value_i17 h_241 _Host_i18 _rep_i18 _value_i18 h_243 _Host_i19 _rep_i19 _value_i19 h_245 _Host_i20 _rep_i20 _value_i20 h_259
          have h_242 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i17 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i17 h_241)
                )
            )
          have h_244 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i18 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i18 h_243)
                )
            )
          let _object_h260 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i17 _value_i18 (Litex.isSet (Litex.R (M := M))) h_241 h_243)))
          have h_260 : Litex.In _value_i20 _object_h260 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i20 _value_i20 (Litex.matrixSet (Litex.R (M := M)) _value_i17 _value_i18 (Litex.isSet (Litex.R (M := M))) h_241 h_243) _object_h260 (Litex.sameRefl _value_i20) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i17 _value_i18 (Litex.isSet (Litex.R (M := M))) h_241 h_243))) h_259)
                )
            )
          let _object_w33 := (Litex.matrixScale _value_i19 _value_i20 _value_i17 _value_i18 (M.real_subset_complex _ h_245) h_241 h_243 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i17 _value_i18 (Litex.isSet (Litex.C (M := M))) h_241 h_243)
            exact (show Litex.In _value_i20 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
              let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i27 : M.Value) (_raw_i28 : M.Value), M.mem _raw_i27 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 h_241))) → M.mem _raw_i28 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i18 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i18 h_243))) → ((fun (_raw_i27 : M.Value) (_raw_i28 : M.Value) => True) _raw_i27 _raw_i28) → True := (by
                  intro _raw_i27 _raw_i28 h_515 h_520 _
                  let _value_i27 := Litex.semanticObject (M := M) _raw_i27 (M.member_isSet h_515)
                  have h_515 : Litex.In _value_i27 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 h_241)) := h_515
                  have h_516 : Litex.In _value_i27 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 h_241)) _value_i27 h_515).1
                        )
                    )
                  have h_517 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i27 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 h_241)) _value_i27 h_515).2.1
                        )
                    )
                  have h_518 : Litex.Le _value_i27 _value_i17 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 h_241)) _value_i27 h_515).2.2
                        )
                    )
                  have h_519 : Litex.In _value_i27 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 h_241)) _value_i27 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_515)
                        )
                    )
                  let _value_i28 := Litex.semanticObject (M := M) _raw_i28 (M.member_isSet h_520)
                  have h_520 : Litex.In _value_i28 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i18 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i18 h_243)) := h_520
                  have h_521 : Litex.In _value_i28 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i18 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i18 h_243)) _value_i28 h_520).1
                        )
                    )
                  have h_522 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i28 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i18 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i18 h_243)) _value_i28 h_520).2.1
                        )
                    )
                  have h_523 : Litex.Le _value_i28 _value_i18 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i18 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i18 h_243)) _value_i28 h_520).2.2
                        )
                    )
                  have h_524 : Litex.In _value_i28 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i18 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i18 h_243)) _value_i28 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_520)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 h_241))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i18 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i18 h_243)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 h_241))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i18 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i18 h_243)))] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 h_241)))
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i18 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i18 h_243)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i27 : M.Value) (_raw_i28 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
              exact (Litex.inOfSame _value_i20 _value_i20 _object_h260 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h260
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                exact (show Litex.Same _left _right from rfl)) h_260))))))
          have h_211 : (by
            let _atomic_wd_1_0 := _object_w33
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.R (M := M)) _value_i17 _value_i18 (Litex.isSet (Litex.R (M := M))) h_241 h_243)
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w33
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.R (M := M)) _value_i17 _value_i18 (Litex.isSet (Litex.R (M := M))) h_241 h_243)
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.rows (_litex_matrix).val.cols .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixScaleInRealFnSet _litex_matrix (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i33 : M.Value) (_raw_i34 : M.Value), M.mem _raw_i33 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 h_241))) → M.mem _raw_i34 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i18 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i18 h_243))) → ((fun (_raw_i33 : M.Value) (_raw_i34 : M.Value) => True) _raw_i33 _raw_i34) → True := (by
                          intro _raw_i33 _raw_i34 h_627 h_632 _
                          let _value_i33 := Litex.semanticObject (M := M) _raw_i33 (M.member_isSet h_627)
                          have h_627 : Litex.In _value_i33 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 h_241)) := h_627
                          have h_628 : Litex.In _value_i33 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 h_241)) _value_i33 h_627).1
                                )
                            )
                          have h_629 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i33 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 h_241)) _value_i33 h_627).2.1
                                )
                            )
                          have h_630 : Litex.Le _value_i33 _value_i17 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 h_241)) _value_i33 h_627).2.2
                                )
                            )
                          have h_631 : Litex.In _value_i33 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 h_241)) _value_i33 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_627)
                                )
                            )
                          let _value_i34 := Litex.semanticObject (M := M) _raw_i34 (M.member_isSet h_632)
                          have h_632 : Litex.In _value_i34 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i18 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i18 h_243)) := h_632
                          have h_633 : Litex.In _value_i34 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i18 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i18 h_243)) _value_i34 h_632).1
                                )
                            )
                          have h_634 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i34 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i18 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i18 h_243)) _value_i34 h_632).2.1
                                )
                            )
                          have h_635 : Litex.Le _value_i34 _value_i18 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i18 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i18 h_243)) _value_i34 h_632).2.2
                                )
                            )
                          have h_636 : Litex.In _value_i34 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i18 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i18 h_243)) _value_i34 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_632)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 h_241))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i18 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i18 h_243)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 h_241))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i18 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i18 h_243)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 h_241)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i18 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i18 h_243)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i33 : M.Value) (_raw_i34 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                      exact (Litex.inOfSame _value_i20 _value_i20 _object_h260 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h260
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_260)) h_245))))
                )
            )
          let _object_h660 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i17 _value_i18 (Litex.isSet (Litex.R (M := M))) h_241 h_243)))
          have h_660 : Litex.In _object_w33 _object_h660 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _object_w33 _object_w33 (Litex.matrixSet (Litex.R (M := M)) _value_i17 _value_i18 (Litex.isSet (Litex.R (M := M))) h_241 h_243) _object_h660 (Litex.sameRefl _object_w33) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i17 _value_i18 (Litex.isSet (Litex.R (M := M))) h_241 h_243))) h_211)
                )
            )
          exact h_211
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_scale_x2f_statement_x2e_lit
