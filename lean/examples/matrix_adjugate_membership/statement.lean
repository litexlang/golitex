import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_adjugate_x5f_membership_x2f_statement_x2e_lit

universe u v1 v2 v15 v16
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_19 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_32 : Litex.In _value_i2 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19)), (by
  let _object_w9 := (Litex.matrixAdjugate _value_i2 _value_i1 h_19 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19)
    exact h_32))
  exact (by
    let _atomic_wd_1_0 := _object_w9
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19)
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_19 _Host_i2 _rep_i2 _value_i2 h_32
          have h_20 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i1 h_19)
                )
            )
          let _object_h33 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19)))
          have h_33 : Litex.In _value_i2 _object_h33 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i2 _value_i2 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19) _object_h33 (Litex.sameRefl _value_i2) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19))) h_32)
                )
            )
          let _object_w9 := (Litex.matrixAdjugate _value_i2 _value_i1 h_19 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19)
            exact h_32))
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
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.order (_litex_matrix).val.order .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixAdjugateInFnSet _litex_matrix))))
                )
            )
          let _object_h136 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19)))
          have h_136 : Litex.In _object_w9 _object_h136 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _object_w9 _object_w9 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19) _object_h136 (Litex.sameRefl _object_w9) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) h_19 h_19))) h_1)
                )
            )
          exact h_1
        )
      )
  )

theorem h_138 : ∀ {_Host_i15 : Type v15} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_155 : Litex.In _value_i15 (Litex.N (M := M))) {_Host_i16 : Type v16} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_168 : Litex.In _value_i16 (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_155 h_155)), (by
  let _object_h169 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_155 h_155)))
  have h_169 : Litex.In _value_i16 _object_h169 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i16 _value_i16 (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_155 h_155) _object_h169 (Litex.sameRefl _value_i16) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_155 h_155))) h_168)
        )
    )
  let _object_w27 := (Litex.matrixAdjugate _value_i16 _value_i15 h_155 (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.C (M := M))) h_155 h_155)
    exact (show Litex.In _value_i16 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i23 : M.Value) (_raw_i24 : M.Value), M.mem _raw_i23 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155))) → M.mem _raw_i24 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155))) → ((fun (_raw_i23 : M.Value) (_raw_i24 : M.Value) => True) _raw_i23 _raw_i24) → True := (by
          intro _raw_i23 _raw_i24 h_333 h_338 _
          let _value_i23 := Litex.semanticObject (M := M) _raw_i23 (M.member_isSet h_333)
          have h_333 : Litex.In _value_i23 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) := h_333
          have h_334 : Litex.In _value_i23 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) _value_i23 h_333).1
                )
            )
          have h_335 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i23 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) _value_i23 h_333).2.1
                )
            )
          have h_336 : Litex.Le _value_i23 _value_i15 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) _value_i23 h_333).2.2
                )
            )
          have h_337 : Litex.In _value_i23 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) _value_i23 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_333)
                )
            )
          let _value_i24 := Litex.semanticObject (M := M) _raw_i24 (M.member_isSet h_338)
          have h_338 : Litex.In _value_i24 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) := h_338
          have h_339 : Litex.In _value_i24 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) _value_i24 h_338).1
                )
            )
          have h_340 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i24 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) _value_i24 h_338).2.1
                )
            )
          have h_341 : Litex.Le _value_i24 _value_i15 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) _value_i24 h_338).2.2
                )
            )
          have h_342 : Litex.In _value_i24 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) _value_i24 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_338)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)))
        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i23 : M.Value) (_raw_i24 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
      exact (Litex.inOfSame _value_i16 _value_i16 _object_h169 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h169
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_169))))))
  exact (by
    let _atomic_wd_1_0 := _object_w27
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_155 h_155)
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i15 _rep_i15 _value_i15 h_155 _Host_i16 _rep_i16 _value_i16 h_168
          have h_156 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i15 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i15 h_155)
                )
            )
          let _object_h169 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_155 h_155)))
          have h_169 : Litex.In _value_i16 _object_h169 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i16 _value_i16 (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_155 h_155) _object_h169 (Litex.sameRefl _value_i16) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_155 h_155))) h_168)
                )
            )
          let _object_w27 := (Litex.matrixAdjugate _value_i16 _value_i15 h_155 (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.C (M := M))) h_155 h_155)
            exact (show Litex.In _value_i16 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
              let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i23 : M.Value) (_raw_i24 : M.Value), M.mem _raw_i23 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155))) → M.mem _raw_i24 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155))) → ((fun (_raw_i23 : M.Value) (_raw_i24 : M.Value) => True) _raw_i23 _raw_i24) → True := (by
                  intro _raw_i23 _raw_i24 h_333 h_338 _
                  let _value_i23 := Litex.semanticObject (M := M) _raw_i23 (M.member_isSet h_333)
                  have h_333 : Litex.In _value_i23 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) := h_333
                  have h_334 : Litex.In _value_i23 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) _value_i23 h_333).1
                        )
                    )
                  have h_335 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i23 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) _value_i23 h_333).2.1
                        )
                    )
                  have h_336 : Litex.Le _value_i23 _value_i15 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) _value_i23 h_333).2.2
                        )
                    )
                  have h_337 : Litex.In _value_i23 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) _value_i23 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_333)
                        )
                    )
                  let _value_i24 := Litex.semanticObject (M := M) _raw_i24 (M.member_isSet h_338)
                  have h_338 : Litex.In _value_i24 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) := h_338
                  have h_339 : Litex.In _value_i24 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) _value_i24 h_338).1
                        )
                    )
                  have h_340 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i24 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) _value_i24 h_338).2.1
                        )
                    )
                  have h_341 : Litex.Le _value_i24 _value_i15 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) _value_i24 h_338).2.2
                        )
                    )
                  have h_342 : Litex.In _value_i24 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) _value_i24 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_338)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)))] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)))
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i23 : M.Value) (_raw_i24 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
              exact (Litex.inOfSame _value_i16 _value_i16 _object_h169 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h169
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                exact (show Litex.Same _left _right from rfl)) h_169))))))
          have h_137 : (by
            let _atomic_wd_1_0 := _object_w27
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_155 h_155)
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w27
                    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_155 h_155)
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixEntrywiseSignature (_litex_matrix).val.order (_litex_matrix).val.order .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixAdjugateInRealFnSet _litex_matrix (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i29 : M.Value) (_raw_i30 : M.Value), M.mem _raw_i29 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155))) → M.mem _raw_i30 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155))) → ((fun (_raw_i29 : M.Value) (_raw_i30 : M.Value) => True) _raw_i29 _raw_i30) → True := (by
                          intro _raw_i29 _raw_i30 h_412 h_417 _
                          let _value_i29 := Litex.semanticObject (M := M) _raw_i29 (M.member_isSet h_412)
                          have h_412 : Litex.In _value_i29 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) := h_412
                          have h_413 : Litex.In _value_i29 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) _value_i29 h_412).1
                                )
                            )
                          have h_414 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i29 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) _value_i29 h_412).2.1
                                )
                            )
                          have h_415 : Litex.Le _value_i29 _value_i15 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) _value_i29 h_412).2.2
                                )
                            )
                          have h_416 : Litex.In _value_i29 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) _value_i29 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_412)
                                )
                            )
                          let _value_i30 := Litex.semanticObject (M := M) _raw_i30 (M.member_isSet h_417)
                          have h_417 : Litex.In _value_i30 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) := h_417
                          have h_418 : Litex.In _value_i30 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) _value_i30 h_417).1
                                )
                            )
                          have h_419 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i30 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) _value_i30 h_417).2.1
                                )
                            )
                          have h_420 : Litex.Le _value_i30 _value_i15 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) _value_i30 h_417).2.2
                                )
                            )
                          have h_421 : Litex.In _value_i30 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)) _value_i30 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_417)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i15 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i15 h_155)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i29 : M.Value) (_raw_i30 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                      exact (Litex.inOfSame _value_i16 _value_i16 _object_h169 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h169
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_169))))))
                )
            )
          let _object_h432 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_155 h_155)))
          have h_432 : Litex.In _object_w27 _object_h432 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _object_w27 _object_w27 (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_155 h_155) _object_h432 (Litex.sameRefl _object_w27) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i15 _value_i15 (Litex.isSet (Litex.R (M := M))) h_155 h_155))) h_137)
                )
            )
          exact h_137
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_adjugate_x5f_membership_x2f_statement_x2e_lit
