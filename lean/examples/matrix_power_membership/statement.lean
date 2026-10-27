import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_power_x5f_membership_x2f_statement_x2e_lit

universe u v1 v2 v3 v19 v20 v21
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_19 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_21 : Litex.In _value_i2 (Litex.N (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_34 : Litex.In _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19)), (by
  let _object_w9 := (Litex.matrixPower _value_i3 _value_i1 _value_i2 h_19 h_21 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19)
    exact h_34))
  exact (by
    let _atomic_wd_1_0 := _object_w9
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19)
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_19 _Host_i2 _rep_i2 _value_i2 h_21 _Host_i3 _rep_i3 _value_i3 h_34
          have h_20 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_19)
                )
            )
          have h_22 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i2 h_21)
                )
            )
          let _object_h35 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19)))
          have h_35 : Litex.In _value_i3 _object_h35 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i3 _value_i3 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19) _object_h35 (Litex.sameRefl _value_i3) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19))) h_34)
                )
            )
          let _object_w9 := (Litex.matrixPower _value_i3 _value_i1 _value_i2 h_19 h_21 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19)
            exact h_34))
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w9
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19)
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w9
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19)
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.order (_litex_matrix).val.order .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixPowerInFnSet _litex_matrix))))
                )
            )
          let _object_h165 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19)))
          have h_165 : Litex.In _object_w9 _object_h165 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _object_w9 _object_w9 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19) _object_h165 (Litex.sameRefl _object_w9) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19))) h_1)
                )
            )
          exact h_1
        )
      )
  )

theorem h_167 : ∀ {_Host_i19 : Type v19} [_rep_i19 : Litex.Representation M _Host_i19] (_value_i19 : Litex.Obj (M := M) _Host_i19) (h_184 : Litex.In _value_i19 (Litex.N (M := M))) {_Host_i20 : Type v20} [_rep_i20 : Litex.Representation M _Host_i20] (_value_i20 : Litex.Obj (M := M) _Host_i20) (h_186 : Litex.In _value_i20 (Litex.N (M := M))) {_Host_i21 : Type v21} [_rep_i21 : Litex.Representation M _Host_i21] (_value_i21 : Litex.Obj (M := M) _Host_i21) (h_199 : Litex.In _value_i21 (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i19 (Litex.isSet (Litex.R (M := M))) h_184 h_184)), (by
  let _object_h200 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i19 (Litex.isSet (Litex.R (M := M))) h_184 h_184)))
  have h_200 : Litex.In _value_i21 _object_h200 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i21 _value_i21 (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i19 (Litex.isSet (Litex.R (M := M))) h_184 h_184) _object_h200 (Litex.sameRefl _value_i21) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i19 (Litex.isSet (Litex.R (M := M))) h_184 h_184))) h_199)
        )
    )
  let _object_w27 := (Litex.matrixPower _value_i21 _value_i19 _value_i20 h_184 h_186 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i19 _value_i19 (Litex.isSet (Litex.C (M := M))) h_184 h_184)
    exact (show Litex.In _value_i21 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i28 : M.Value) (_raw_i29 : M.Value), M.mem _raw_i28 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184))) → M.mem _raw_i29 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184))) → ((fun (_raw_i28 : M.Value) (_raw_i29 : M.Value) => True) _raw_i28 _raw_i29) → True := (by
          intro _raw_i28 _raw_i29 h_399 h_404 _
          let _value_i28 := Litex.semanticObject (M := M) _raw_i28 (M.member_isSet h_399)
          have h_399 : Litex.In _value_i28 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) := h_399
          have h_400 : Litex.In _value_i28 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) _value_i28 h_399).1
                )
            )
          have h_401 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i28 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) _value_i28 h_399).2.1
                )
            )
          have h_402 : Litex.Le _value_i28 _value_i19 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) _value_i28 h_399).2.2
                )
            )
          have h_403 : Litex.In _value_i28 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) _value_i28 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_399)
                )
            )
          let _value_i29 := Litex.semanticObject (M := M) _raw_i29 (M.member_isSet h_404)
          have h_404 : Litex.In _value_i29 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) := h_404
          have h_405 : Litex.In _value_i29 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) _value_i29 h_404).1
                )
            )
          have h_406 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i29 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) _value_i29 h_404).2.1
                )
            )
          have h_407 : Litex.Le _value_i29 _value_i19 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) _value_i29 h_404).2.2
                )
            )
          have h_408 : Litex.In _value_i29 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) _value_i29 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_404)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)))
        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i28 : M.Value) (_raw_i29 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
      exact (Litex.inOfSame _value_i21 _value_i21 _object_h200 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h200
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_200))))))
  exact (by
    let _atomic_wd_1_0 := _object_w27
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i19 (Litex.isSet (Litex.R (M := M))) h_184 h_184)
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i19 _rep_i19 _value_i19 h_184 _Host_i20 _rep_i20 _value_i20 h_186 _Host_i21 _rep_i21 _value_i21 h_199
          have h_185 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i19 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i19 h_184)
                )
            )
          have h_187 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i20 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i20 h_186)
                )
            )
          let _object_h200 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i19 (Litex.isSet (Litex.R (M := M))) h_184 h_184)))
          have h_200 : Litex.In _value_i21 _object_h200 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i21 _value_i21 (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i19 (Litex.isSet (Litex.R (M := M))) h_184 h_184) _object_h200 (Litex.sameRefl _value_i21) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i19 (Litex.isSet (Litex.R (M := M))) h_184 h_184))) h_199)
                )
            )
          let _object_w27 := (Litex.matrixPower _value_i21 _value_i19 _value_i20 h_184 h_186 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i19 _value_i19 (Litex.isSet (Litex.C (M := M))) h_184 h_184)
            exact (show Litex.In _value_i21 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
              let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i28 : M.Value) (_raw_i29 : M.Value), M.mem _raw_i28 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184))) → M.mem _raw_i29 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184))) → ((fun (_raw_i28 : M.Value) (_raw_i29 : M.Value) => True) _raw_i28 _raw_i29) → True := (by
                  intro _raw_i28 _raw_i29 h_399 h_404 _
                  let _value_i28 := Litex.semanticObject (M := M) _raw_i28 (M.member_isSet h_399)
                  have h_399 : Litex.In _value_i28 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) := h_399
                  have h_400 : Litex.In _value_i28 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) _value_i28 h_399).1
                        )
                    )
                  have h_401 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i28 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) _value_i28 h_399).2.1
                        )
                    )
                  have h_402 : Litex.Le _value_i28 _value_i19 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) _value_i28 h_399).2.2
                        )
                    )
                  have h_403 : Litex.In _value_i28 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) _value_i28 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_399)
                        )
                    )
                  let _value_i29 := Litex.semanticObject (M := M) _raw_i29 (M.member_isSet h_404)
                  have h_404 : Litex.In _value_i29 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) := h_404
                  have h_405 : Litex.In _value_i29 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) _value_i29 h_404).1
                        )
                    )
                  have h_406 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i29 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) _value_i29 h_404).2.1
                        )
                    )
                  have h_407 : Litex.Le _value_i29 _value_i19 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) _value_i29 h_404).2.2
                        )
                    )
                  have h_408 : Litex.In _value_i29 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) _value_i29 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_404)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)))] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)))
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i28 : M.Value) (_raw_i29 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
              exact (Litex.inOfSame _value_i21 _value_i21 _object_h200 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h200
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                exact (show Litex.Same _left _right from rfl)) h_200))))))
          have h_166 : (by
            let _atomic_wd_1_0 := _object_w27
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i19 (Litex.isSet (Litex.R (M := M))) h_184 h_184)
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w27
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i19 (Litex.isSet (Litex.R (M := M))) h_184 h_184)
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.order (_litex_matrix).val.order .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixPowerInRealFnSet _litex_matrix (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i34 : M.Value) (_raw_i35 : M.Value), M.mem _raw_i34 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184))) → M.mem _raw_i35 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184))) → ((fun (_raw_i34 : M.Value) (_raw_i35 : M.Value) => True) _raw_i34 _raw_i35) → True := (by
                          intro _raw_i34 _raw_i35 h_494 h_499 _
                          let _value_i34 := Litex.semanticObject (M := M) _raw_i34 (M.member_isSet h_494)
                          have h_494 : Litex.In _value_i34 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) := h_494
                          have h_495 : Litex.In _value_i34 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) _value_i34 h_494).1
                                )
                            )
                          have h_496 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i34 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) _value_i34 h_494).2.1
                                )
                            )
                          have h_497 : Litex.Le _value_i34 _value_i19 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) _value_i34 h_494).2.2
                                )
                            )
                          have h_498 : Litex.In _value_i34 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) _value_i34 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_494)
                                )
                            )
                          let _value_i35 := Litex.semanticObject (M := M) _raw_i35 (M.member_isSet h_499)
                          have h_499 : Litex.In _value_i35 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) := h_499
                          have h_500 : Litex.In _value_i35 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) _value_i35 h_499).1
                                )
                            )
                          have h_501 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i35 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) _value_i35 h_499).2.1
                                )
                            )
                          have h_502 : Litex.Le _value_i35 _value_i19 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) _value_i35 h_499).2.2
                                )
                            )
                          have h_503 : Litex.In _value_i35 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)) _value_i35 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_499)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i19 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i19 h_184)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i34 : M.Value) (_raw_i35 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                      exact (Litex.inOfSame _value_i21 _value_i21 _object_h200 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h200
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_200))))))
                )
            )
          let _object_h516 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i19 (Litex.isSet (Litex.R (M := M))) h_184 h_184)))
          have h_516 : Litex.In _object_w27 _object_h516 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _object_w27 _object_w27 (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i19 (Litex.isSet (Litex.R (M := M))) h_184 h_184) _object_h516 (Litex.sameRefl _object_w27) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i19 _value_i19 (Litex.isSet (Litex.R (M := M))) h_184 h_184))) h_166)
                )
            )
          exact h_166
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_power_x5f_membership_x2f_statement_x2e_lit
