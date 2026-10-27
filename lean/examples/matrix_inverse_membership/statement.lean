import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_inverse_x5f_membership_x2f_statement_x2e_lit

universe u v1 v2 v15 v16
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_20 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_33 : Litex.In _value_i2 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_20 h_20)) (h_1 : (by
  let _atomic_wd_1_0 := (Litex.matrixDeterminant _value_i2 _value_i1 h_20 (by
    let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_20 h_20)
    exact h_33))
  exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))), (by
  let _object_w10 := (Litex.matrixInverse _value_i2 _value_i1 h_20 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_20 h_20)
    exact h_33) (by
    let _atomic_wd_1_0 := (Litex.matrixDeterminant _value_i2 _value_i1 h_20 (by
      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_20 h_20)
      exact h_33))
    exact h_1))
  exact (by
    let _atomic_wd_1_0 := _object_w10
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_20 h_20)
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_20 _Host_i2 _rep_i2 _value_i2 h_33 h_1
          have h_21 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_20)
                )
            )
          let _object_h34 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_20 h_20)))
          have h_34 : Litex.In _value_i2 _object_h34 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i2 _value_i2 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_20 h_20) _object_h34 (Litex.sameRefl _value_i2) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_20 h_20))) h_33)
                )
            )
          let _object_w10 := (Litex.matrixInverse _value_i2 _value_i1 h_20 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_20 h_20)
            exact h_33) (by
            let _atomic_wd_1_0 := (Litex.matrixDeterminant _value_i2 _value_i1 h_20 (by
              let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_20 h_20)
              exact h_33))
            exact h_1))
          have h_2 : (by
            let _atomic_wd_1_0 := _object_w10
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_20 h_20)
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w10
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_20 h_20)
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.order (_litex_matrix).val.order .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixInverseInFnSet _litex_matrix))))
                )
            )
          let _object_h154 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_20 h_20)))
          have h_154 : Litex.In _object_w10 _object_h154 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _object_w10 _object_w10 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_20 h_20) _object_h154 (Litex.sameRefl _object_w10) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_20 h_20))) h_2)
                )
            )
          exact h_2
        )
      )
  )

theorem h_157 : ∀ {_Host_i15 : Type v15} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_174 : Litex.In _value_i15 (Litex.N (M := M))) {_Host_i16 : Type v16} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_187 : Litex.In _value_i16 (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_174 h_174)) (h_155 : (by
  let _object_h188 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_174 h_174)))
  have h_188 : Litex.In _value_i16 _object_h188 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i16 _value_i16 (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_174 h_174) _object_h188 (Litex.sameRefl _value_i16) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_174 h_174))) h_187)
        )
    )
  exact (by
    let _atomic_wd_1_0 := (Litex.matrixDeterminant _value_i16 _value_i15 h_174 (by
      let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.C (M := M))) h_174 h_174)
      exact (show Litex.In _value_i16 _atomic_wd_2_1 from (Litex.functionRealToComplex (by
        let _atomic_wd_3_1 := (let _checked_header : ∀ (_raw_i23 : M.Value) (_raw_i24 : M.Value), M.mem _raw_i23 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174))) → M.mem _raw_i24 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174))) → ((fun (_raw_i23 : M.Value) (_raw_i24 : M.Value) => True) _raw_i23 _raw_i24) → True := (by
            intro _raw_i23 _raw_i24 h_352 h_357 _
            let _value_i23 := Litex.semanticObject (M := M) _raw_i23 (M.member_isSet h_352)
            have h_352 : Litex.In _value_i23 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) := h_352
            have h_353 : Litex.In _value_i23 (Litex.Z (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i23 h_352).1
                  )
              )
            have h_354 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i23 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i23 h_352).2.1
                  )
              )
            have h_355 : Litex.Le _value_i23 _value_i15 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i23 h_352).2.2
                  )
              )
            have h_356 : Litex.In _value_i23 (Litex.NPos (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i23 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_352)
                  )
              )
            let _value_i24 := Litex.semanticObject (M := M) _raw_i24 (M.member_isSet h_357)
            have h_357 : Litex.In _value_i24 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) := h_357
            have h_358 : Litex.In _value_i24 (Litex.Z (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i24 h_357).1
                  )
              )
            have h_359 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i24 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i24 h_357).2.1
                  )
              )
            have h_360 : Litex.Le _value_i24 _value_i15 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i24 h_357).2.2
                  )
              )
            have h_361 : Litex.In _value_i24 (Litex.NPos (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i24 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_357)
                  )
              )
            exact True.intro);
          Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)))] (by
          have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)))
          have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i23 : M.Value) (_raw_i24 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
        exact (Litex.inOfSame _value_i16 _value_i16 _object_h188 _atomic_wd_3_1 (show @Eq M.Value _ _ from Eq.refl _) (by
          let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h188
          let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_3_1
          exact (show Litex.Same _left _right from rfl)) h_188))))))
    exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))
)), (by
  let _object_h188 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_174 h_174)))
  have h_188 : Litex.In _value_i16 _object_h188 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i16 _value_i16 (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_174 h_174) _object_h188 (Litex.sameRefl _value_i16) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_174 h_174))) h_187)
        )
    )
  let _object_w37 := (Litex.matrixInverse _value_i16 _value_i15 h_174 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.C (M := M))) h_174 h_174)
    exact (show Litex.In _value_i16 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i29 : M.Value) (_raw_i30 : M.Value), M.mem _raw_i29 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174))) → M.mem _raw_i30 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174))) → ((fun (_raw_i29 : M.Value) (_raw_i30 : M.Value) => True) _raw_i29 _raw_i30) → True := (by
          intro _raw_i29 _raw_i30 h_535 h_540 _
          let _value_i29 := Litex.semanticObject (M := M) _raw_i29 (M.member_isSet h_535)
          have h_535 : Litex.In _value_i29 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) := h_535
          have h_536 : Litex.In _value_i29 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i29 h_535).1
                )
            )
          have h_537 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i29 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i29 h_535).2.1
                )
            )
          have h_538 : Litex.Le _value_i29 _value_i15 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i29 h_535).2.2
                )
            )
          have h_539 : Litex.In _value_i29 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i29 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_535)
                )
            )
          let _value_i30 := Litex.semanticObject (M := M) _raw_i30 (M.member_isSet h_540)
          have h_540 : Litex.In _value_i30 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) := h_540
          have h_541 : Litex.In _value_i30 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i30 h_540).1
                )
            )
          have h_542 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i30 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i30 h_540).2.1
                )
            )
          have h_543 : Litex.Le _value_i30 _value_i15 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i30 h_540).2.2
                )
            )
          have h_544 : Litex.In _value_i30 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i30 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_540)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)))
        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i29 : M.Value) (_raw_i30 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
      exact (Litex.inOfSame _value_i16 _value_i16 _object_h188 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h188
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_188))))) (by
    let _atomic_wd_1_0 := (Litex.matrixDeterminant _value_i16 _value_i15 h_174 (by
      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.C (M := M))) h_174 h_174)
      exact (show Litex.In _value_i16 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
        let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i23 : M.Value) (_raw_i24 : M.Value), M.mem _raw_i23 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174))) → M.mem _raw_i24 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174))) → ((fun (_raw_i23 : M.Value) (_raw_i24 : M.Value) => True) _raw_i23 _raw_i24) → True := (by
            intro _raw_i23 _raw_i24 h_352 h_357 _
            let _value_i23 := Litex.semanticObject (M := M) _raw_i23 (M.member_isSet h_352)
            have h_352 : Litex.In _value_i23 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) := h_352
            have h_353 : Litex.In _value_i23 (Litex.Z (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i23 h_352).1
                  )
              )
            have h_354 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i23 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i23 h_352).2.1
                  )
              )
            have h_355 : Litex.Le _value_i23 _value_i15 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i23 h_352).2.2
                  )
              )
            have h_356 : Litex.In _value_i23 (Litex.NPos (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i23 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_352)
                  )
              )
            let _value_i24 := Litex.semanticObject (M := M) _raw_i24 (M.member_isSet h_357)
            have h_357 : Litex.In _value_i24 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) := h_357
            have h_358 : Litex.In _value_i24 (Litex.Z (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i24 h_357).1
                  )
              )
            have h_359 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i24 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i24 h_357).2.1
                  )
              )
            have h_360 : Litex.Le _value_i24 _value_i15 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i24 h_357).2.2
                  )
              )
            have h_361 : Litex.In _value_i24 (Litex.NPos (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i24 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_357)
                  )
              )
            exact True.intro);
          Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)))] (by
          have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)))
          have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i23 : M.Value) (_raw_i24 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
        exact (Litex.inOfSame _value_i16 _value_i16 _object_h188 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
          let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h188
          let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
          exact (show Litex.Same _left _right from rfl)) h_188))))))
    exact h_155))
  exact (by
    let _atomic_wd_1_0 := _object_w37
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_174 h_174)
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i15 _rep_i15 _value_i15 h_174 _Host_i16 _rep_i16 _value_i16 h_187 h_155
          have h_175 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i15 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i15 h_174)
                )
            )
          let _object_h188 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_174 h_174)))
          have h_188 : Litex.In _value_i16 _object_h188 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i16 _value_i16 (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_174 h_174) _object_h188 (Litex.sameRefl _value_i16) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_174 h_174))) h_187)
                )
            )
          let _object_w37 := (Litex.matrixInverse _value_i16 _value_i15 h_174 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.C (M := M))) h_174 h_174)
            exact (show Litex.In _value_i16 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
              let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i29 : M.Value) (_raw_i30 : M.Value), M.mem _raw_i29 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174))) → M.mem _raw_i30 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174))) → ((fun (_raw_i29 : M.Value) (_raw_i30 : M.Value) => True) _raw_i29 _raw_i30) → True := (by
                  intro _raw_i29 _raw_i30 h_535 h_540 _
                  let _value_i29 := Litex.semanticObject (M := M) _raw_i29 (M.member_isSet h_535)
                  have h_535 : Litex.In _value_i29 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) := h_535
                  have h_536 : Litex.In _value_i29 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i29 h_535).1
                        )
                    )
                  have h_537 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i29 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i29 h_535).2.1
                        )
                    )
                  have h_538 : Litex.Le _value_i29 _value_i15 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i29 h_535).2.2
                        )
                    )
                  have h_539 : Litex.In _value_i29 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i29 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_535)
                        )
                    )
                  let _value_i30 := Litex.semanticObject (M := M) _raw_i30 (M.member_isSet h_540)
                  have h_540 : Litex.In _value_i30 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) := h_540
                  have h_541 : Litex.In _value_i30 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i30 h_540).1
                        )
                    )
                  have h_542 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i30 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i30 h_540).2.1
                        )
                    )
                  have h_543 : Litex.Le _value_i30 _value_i15 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i30 h_540).2.2
                        )
                    )
                  have h_544 : Litex.In _value_i30 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i30 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_540)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)))] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)))
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i29 : M.Value) (_raw_i30 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
              exact (Litex.inOfSame _value_i16 _value_i16 _object_h188 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h188
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                exact (show Litex.Same _left _right from rfl)) h_188))))) (by
            let _atomic_wd_1_0 := (Litex.matrixDeterminant _value_i16 _value_i15 h_174 (by
              let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.C (M := M))) h_174 h_174)
              exact (show Litex.In _value_i16 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
                let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i23 : M.Value) (_raw_i24 : M.Value), M.mem _raw_i23 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174))) → M.mem _raw_i24 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174))) → ((fun (_raw_i23 : M.Value) (_raw_i24 : M.Value) => True) _raw_i23 _raw_i24) → True := (by
                    intro _raw_i23 _raw_i24 h_352 h_357 _
                    let _value_i23 := Litex.semanticObject (M := M) _raw_i23 (M.member_isSet h_352)
                    have h_352 : Litex.In _value_i23 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) := h_352
                    have h_353 : Litex.In _value_i23 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i23 h_352).1
                          )
                      )
                    have h_354 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i23 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i23 h_352).2.1
                          )
                      )
                    have h_355 : Litex.Le _value_i23 _value_i15 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i23 h_352).2.2
                          )
                      )
                    have h_356 : Litex.In _value_i23 (Litex.NPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i23 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_352)
                          )
                      )
                    let _value_i24 := Litex.semanticObject (M := M) _raw_i24 (M.member_isSet h_357)
                    have h_357 : Litex.In _value_i24 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) := h_357
                    have h_358 : Litex.In _value_i24 (Litex.Z (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i24 h_357).1
                          )
                      )
                    have h_359 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i24 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i24 h_357).2.1
                          )
                      )
                    have h_360 : Litex.Le _value_i24 _value_i15 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i24 h_357).2.2
                          )
                      )
                    have h_361 : Litex.In _value_i24 (Litex.NPos (M := M)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i24 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_357)
                          )
                      )
                    exact True.intro);
                  Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)))] (by
                  have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)))
                  have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)))
                  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i23 : M.Value) (_raw_i24 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                exact (Litex.inOfSame _value_i16 _value_i16 _object_h188 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                  let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h188
                  let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                  exact (show Litex.Same _left _right from rfl)) h_188))))))
            exact h_155))
          have h_156 : (by
            let _atomic_wd_1_0 := _object_w37
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_174 h_174)
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w37
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_174 h_174)
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.order (_litex_matrix).val.order .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixInverseInRealFnSet _litex_matrix (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i35 : M.Value) (_raw_i36 : M.Value), M.mem _raw_i35 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174))) → M.mem _raw_i36 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174))) → ((fun (_raw_i35 : M.Value) (_raw_i36 : M.Value) => True) _raw_i35 _raw_i36) → True := (by
                          intro _raw_i35 _raw_i36 h_619 h_624 _
                          let _value_i35 := Litex.semanticObject (M := M) _raw_i35 (M.member_isSet h_619)
                          have h_619 : Litex.In _value_i35 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) := h_619
                          have h_620 : Litex.In _value_i35 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i35 h_619).1
                                )
                            )
                          have h_621 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i35 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i35 h_619).2.1
                                )
                            )
                          have h_622 : Litex.Le _value_i35 _value_i15 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i35 h_619).2.2
                                )
                            )
                          have h_623 : Litex.In _value_i35 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i35 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_619)
                                )
                            )
                          let _value_i36 := Litex.semanticObject (M := M) _raw_i36 (M.member_isSet h_624)
                          have h_624 : Litex.In _value_i36 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) := h_624
                          have h_625 : Litex.In _value_i36 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i36 h_624).1
                                )
                            )
                          have h_626 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i36 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i36 h_624).2.1
                                )
                            )
                          have h_627 : Litex.Le _value_i36 _value_i15 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i36 h_624).2.2
                                )
                            )
                          have h_628 : Litex.In _value_i36 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)) _value_i36 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_624)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_174)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i35 : M.Value) (_raw_i36 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                      exact (Litex.inOfSame _value_i16 _value_i16 _object_h188 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h188
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_188))))))
                )
            )
          let _object_h639 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_174 h_174)))
          have h_639 : Litex.In _object_w37 _object_h639 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _object_w37 _object_w37 (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_174 h_174) _object_h639 (Litex.sameRefl _object_w37) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_174 h_174))) h_156)
                )
            )
          exact h_156
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_inverse_x5f_membership_x2f_statement_x2e_lit
