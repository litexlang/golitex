import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_minor_x5f_membership_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v17 v18 v19 v20
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_22 : Litex.In _value_i1 (Litex.NPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_47 : Litex.In _value_i2 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) (Litex.inNPos_natural _value_i1 h_22) (Litex.inNPos_natural _value_i1 h_22))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_77 : Litex.In _value_i3 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22)))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_82 : Litex.In _value_i4 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22)))), (by
  have h_23 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inNPos_positive _value_i1 h_22)
        )
    )
  let _object_w8 := (Litex.matrixMinor _value_i2 _value_i1 _value_i3 _value_i4 h_22 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22)))
    exact h_77) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22)))
    exact h_82) (Litex.inNPos_natural _value_i1 h_22) (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) (Litex.inNPos_natural _value_i1 h_22) (Litex.inNPos_natural _value_i1 h_22))
    exact h_47))
  let _object_w9 := (let _wd_1_0 := (Litex.C (M := M));
  let _wd_1_1 := (Litex.sub _value_i1 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i1 (Litex.inNPos_natural _value_i1 h_22)) (Litex.numberInC (M := M) (1 : ℂ)));
  let _wd_1_2 := _wd_1_1;
  (Litex.matrixSet _wd_1_0 _wd_1_1 _wd_1_2 (Litex.isSet _wd_1_0) (by
    let _atomic_wd_1_0 := _wd_1_2
    exact (Litex.integerToNaturalOfNonnegative _atomic_wd_1_0 (by
      let _atomic_wd_2_0 := _atomic_wd_1_0
      exact (Litex.subInZ _value_i1 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) (by
      let _atomic_wd_2_1 := _atomic_wd_1_0
      exact (Litex.integerPredecessorLe (Litex.number (M := M) (0 : ℂ)) _atomic_wd_2_1 (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22)) (Litex.sameRefl (Litex.number (M := M) 1)) h_23)))) (by
    let _atomic_wd_1_0 := _wd_1_2
    exact (Litex.integerToNaturalOfNonnegative _atomic_wd_1_0 (by
      let _atomic_wd_2_0 := _atomic_wd_1_0
      exact (Litex.subInZ _value_i1 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) (by
      let _atomic_wd_2_1 := _atomic_wd_1_0
      exact (Litex.integerPredecessorLe (Litex.number (M := M) (0 : ℂ)) _atomic_wd_2_1 (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22)) (Litex.sameRefl (Litex.number (M := M) 1)) h_23))))))
  exact (by
    let _atomic_wd_1_0 := _object_w8
    let _atomic_wd_1_1 := _object_w9
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_22 _Host_i2 _rep_i2 _value_i2 h_47 _Host_i3 _rep_i3 _value_i3 h_77 _Host_i4 _rep_i4 _value_i4 h_82
          have h_23 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inNPos_positive _value_i1 h_22)
                )
            )
          have h_24 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i1 h_23)
                )
            )
          have h_25 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i1 h_23) _litex_zero.symm)
                )
            )
          let _object_h48 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) (Litex.inNPos_natural _value_i1 h_22) (Litex.inNPos_natural _value_i1 h_22))))
          have h_48 : Litex.In _value_i2 _object_h48 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i2 _value_i2 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) (Litex.inNPos_natural _value_i1 h_22) (Litex.inNPos_natural _value_i1 h_22)) _object_h48 (Litex.sameRefl _value_i2) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) (Litex.inNPos_natural _value_i1 h_22) (Litex.inNPos_natural _value_i1 h_22)))) h_47)
                )
            )
          have h_78 : Litex.In _value_i3 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22))) _value_i3 h_77).1
                )
            )
          have h_79 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22))) _value_i3 h_77).2.1
                )
            )
          have h_80 : Litex.Le _value_i3 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22))) _value_i3 h_77).2.2
                )
            )
          have h_81 : Litex.In _value_i3 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22))) _value_i3 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_77)
                )
            )
          have h_83 : Litex.In _value_i4 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22))) _value_i4 h_82).1
                )
            )
          have h_84 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22))) _value_i4 h_82).2.1
                )
            )
          have h_85 : Litex.Le _value_i4 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22))) _value_i4 h_82).2.2
                )
            )
          have h_86 : Litex.In _value_i4 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22))) _value_i4 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_82)
                )
            )
          let _object_w8 := (Litex.matrixMinor _value_i2 _value_i1 _value_i3 _value_i4 h_22 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22)))
            exact h_77) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22)))
            exact h_82) (Litex.inNPos_natural _value_i1 h_22) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) (Litex.inNPos_natural _value_i1 h_22) (Litex.inNPos_natural _value_i1 h_22))
            exact h_47))
          let _object_w9 := (let _wd_1_0 := (Litex.C (M := M));
          let _wd_1_1 := (Litex.sub _value_i1 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i1 (Litex.inNPos_natural _value_i1 h_22)) (Litex.numberInC (M := M) (1 : ℂ)));
          let _wd_1_2 := _wd_1_1;
          (Litex.matrixSet _wd_1_0 _wd_1_1 _wd_1_2 (Litex.isSet _wd_1_0) (by
            let _atomic_wd_1_0 := _wd_1_2
            exact (Litex.integerToNaturalOfNonnegative _atomic_wd_1_0 (by
              let _atomic_wd_2_0 := _atomic_wd_1_0
              exact (Litex.subInZ _value_i1 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) (by
              let _atomic_wd_2_1 := _atomic_wd_1_0
              exact (Litex.integerPredecessorLe (Litex.number (M := M) (0 : ℂ)) _atomic_wd_2_1 (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22)) (Litex.sameRefl (Litex.number (M := M) 1)) h_23)))) (by
            let _atomic_wd_1_0 := _wd_1_2
            exact (Litex.integerToNaturalOfNonnegative _atomic_wd_1_0 (by
              let _atomic_wd_2_0 := _atomic_wd_1_0
              exact (Litex.subInZ _value_i1 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) (by
              let _atomic_wd_2_1 := _atomic_wd_1_0
              exact (Litex.integerPredecessorLe (Litex.number (M := M) (0 : ℂ)) _atomic_wd_2_1 (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22)) (Litex.sameRefl (Litex.number (M := M) 1)) h_23))))))
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w8
            let _atomic_wd_1_1 := _object_w9
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w8
                    let _atomic_wd_1_1 := _object_w9
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixMinorSignature (_litex_matrix).val.order .complex); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixMinorInFnSet _litex_matrix))))
                )
            )
          let _object_h6468 := (Litex.fnSet (Litex.matrixSignature _object_w9))
          have h_6468 : Litex.In _object_w8 _object_h6468 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _object_w8 _object_w8 _object_w9 _object_h6468 (Litex.sameRefl _object_w8) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet _object_w9)) h_1)
                )
            )
          exact h_1
        )
      )
  )

theorem h_6470 : ∀ {_Host_i17 : Type v17} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_6490 : Litex.In _value_i17 (Litex.NPos (M := M))) {_Host_i18 : Type v18} [_rep_i18 : Litex.Representation M _Host_i18] (_value_i18 : Litex.Obj (M := M) _Host_i18) (h_6515 : Litex.In _value_i18 (Litex.matrixSet (Litex.R (M := M)) _value_i17 _value_i17 (Litex.isSet (Litex.R (M := M))) (Litex.inNPos_natural _value_i17 h_6490) (Litex.inNPos_natural _value_i17 h_6490))) {_Host_i19 : Type v19} [_rep_i19 : Litex.Representation M _Host_i19] (_value_i19 : Litex.Obj (M := M) _Host_i19) (h_6545 : Litex.In _value_i19 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490)))) {_Host_i20 : Type v20} [_rep_i20 : Litex.Representation M _Host_i20] (_value_i20 : Litex.Obj (M := M) _Host_i20) (h_6550 : Litex.In _value_i20 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490)))), (by
  have h_6491 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i17 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inNPos_positive _value_i17 h_6490)
        )
    )
  let _object_h6516 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i17 _value_i17 (Litex.isSet (Litex.R (M := M))) (Litex.inNPos_natural _value_i17 h_6490) (Litex.inNPos_natural _value_i17 h_6490))))
  have h_6516 : Litex.In _value_i18 _object_h6516 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i18 _value_i18 (Litex.matrixSet (Litex.R (M := M)) _value_i17 _value_i17 (Litex.isSet (Litex.R (M := M))) (Litex.inNPos_natural _value_i17 h_6490) (Litex.inNPos_natural _value_i17 h_6490)) _object_h6516 (Litex.sameRefl _value_i18) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i17 _value_i17 (Litex.isSet (Litex.R (M := M))) (Litex.inNPos_natural _value_i17 h_6490) (Litex.inNPos_natural _value_i17 h_6490)))) h_6515)
        )
    )
  let _object_w18 := (Litex.matrixMinor _value_i18 _value_i17 _value_i19 _value_i20 h_6490 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490)))
    exact h_6545) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490)))
    exact h_6550) (Litex.inNPos_natural _value_i17 h_6490) (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i17 _value_i17 (Litex.isSet (Litex.C (M := M))) (Litex.inNPos_natural _value_i17 h_6490) (Litex.inNPos_natural _value_i17 h_6490))
    exact (show Litex.In _value_i18 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i27 : M.Value) (_raw_i28 : M.Value), M.mem _raw_i27 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490)))) → M.mem _raw_i28 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490)))) → ((fun (_raw_i27 : M.Value) (_raw_i28 : M.Value) => True) _raw_i27 _raw_i28) → True := (by
          intro _raw_i27 _raw_i28 h_6794 h_6799 _
          let _value_i27 := Litex.semanticObject (M := M) _raw_i27 (M.member_isSet h_6794)
          have h_6794 : Litex.In _value_i27 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) := h_6794
          have h_6795 : Litex.In _value_i27 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i27 h_6794).1
                )
            )
          have h_6796 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i27 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i27 h_6794).2.1
                )
            )
          have h_6797 : Litex.Le _value_i27 _value_i17 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i27 h_6794).2.2
                )
            )
          have h_6798 : Litex.In _value_i27 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i27 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6794)
                )
            )
          let _value_i28 := Litex.semanticObject (M := M) _raw_i28 (M.member_isSet h_6799)
          have h_6799 : Litex.In _value_i28 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) := h_6799
          have h_6800 : Litex.In _value_i28 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i28 h_6799).1
                )
            )
          have h_6801 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i28 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i28 h_6799).2.1
                )
            )
          have h_6802 : Litex.Le _value_i28 _value_i17 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i28 h_6799).2.2
                )
            )
          have h_6803 : Litex.In _value_i28 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i28 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6799)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))))
        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i27 : M.Value) (_raw_i28 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
      exact (Litex.inOfSame _value_i18 _value_i18 _object_h6516 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h6516
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_6516))))))
  let _object_w19 := (let _wd_1_0 := (Litex.R (M := M));
  let _wd_1_1 := (Litex.sub _value_i17 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i17 (Litex.inNPos_natural _value_i17 h_6490)) (Litex.numberInC (M := M) (1 : ℂ)));
  let _wd_1_2 := _wd_1_1;
  (Litex.matrixSet _wd_1_0 _wd_1_1 _wd_1_2 (Litex.isSet _wd_1_0) (by
    let _atomic_wd_1_0 := _wd_1_2
    exact (Litex.integerToNaturalOfNonnegative _atomic_wd_1_0 (by
      let _atomic_wd_2_0 := _atomic_wd_1_0
      exact (Litex.subInZ _value_i17 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) (by
      let _atomic_wd_2_1 := _atomic_wd_1_0
      exact (Litex.integerPredecessorLe (Litex.number (M := M) (0 : ℂ)) _atomic_wd_2_1 (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490)) (Litex.sameRefl (Litex.number (M := M) 1)) h_6491)))) (by
    let _atomic_wd_1_0 := _wd_1_2
    exact (Litex.integerToNaturalOfNonnegative _atomic_wd_1_0 (by
      let _atomic_wd_2_0 := _atomic_wd_1_0
      exact (Litex.subInZ _value_i17 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) (by
      let _atomic_wd_2_1 := _atomic_wd_1_0
      exact (Litex.integerPredecessorLe (Litex.number (M := M) (0 : ℂ)) _atomic_wd_2_1 (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490)) (Litex.sameRefl (Litex.number (M := M) 1)) h_6491))))))
  exact (by
    let _atomic_wd_1_0 := _object_w18
    let _atomic_wd_1_1 := _object_w19
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i17 _rep_i17 _value_i17 h_6490 _Host_i18 _rep_i18 _value_i18 h_6515 _Host_i19 _rep_i19 _value_i19 h_6545 _Host_i20 _rep_i20 _value_i20 h_6550
          have h_6491 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i17 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inNPos_positive _value_i17 h_6490)
                )
            )
          have h_6492 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i17 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i17 h_6491)
                )
            )
          have h_6493 : ¬ Litex.Same _value_i17 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i17 h_6491) _litex_zero.symm)
                )
            )
          let _object_h6516 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i17 _value_i17 (Litex.isSet (Litex.R (M := M))) (Litex.inNPos_natural _value_i17 h_6490) (Litex.inNPos_natural _value_i17 h_6490))))
          have h_6516 : Litex.In _value_i18 _object_h6516 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i18 _value_i18 (Litex.matrixSet (Litex.R (M := M)) _value_i17 _value_i17 (Litex.isSet (Litex.R (M := M))) (Litex.inNPos_natural _value_i17 h_6490) (Litex.inNPos_natural _value_i17 h_6490)) _object_h6516 (Litex.sameRefl _value_i18) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i17 _value_i17 (Litex.isSet (Litex.R (M := M))) (Litex.inNPos_natural _value_i17 h_6490) (Litex.inNPos_natural _value_i17 h_6490)))) h_6515)
                )
            )
          have h_6546 : Litex.In _value_i19 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i19 h_6545).1
                )
            )
          have h_6547 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i19 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i19 h_6545).2.1
                )
            )
          have h_6548 : Litex.Le _value_i19 _value_i17 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i19 h_6545).2.2
                )
            )
          have h_6549 : Litex.In _value_i19 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i19 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6545)
                )
            )
          have h_6551 : Litex.In _value_i20 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i20 h_6550).1
                )
            )
          have h_6552 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i20 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i20 h_6550).2.1
                )
            )
          have h_6553 : Litex.Le _value_i20 _value_i17 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i20 h_6550).2.2
                )
            )
          have h_6554 : Litex.In _value_i20 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i20 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6550)
                )
            )
          let _object_w18 := (Litex.matrixMinor _value_i18 _value_i17 _value_i19 _value_i20 h_6490 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490)))
            exact h_6545) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490)))
            exact h_6550) (Litex.inNPos_natural _value_i17 h_6490) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i17 _value_i17 (Litex.isSet (Litex.C (M := M))) (Litex.inNPos_natural _value_i17 h_6490) (Litex.inNPos_natural _value_i17 h_6490))
            exact (show Litex.In _value_i18 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
              let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i27 : M.Value) (_raw_i28 : M.Value), M.mem _raw_i27 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490)))) → M.mem _raw_i28 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490)))) → ((fun (_raw_i27 : M.Value) (_raw_i28 : M.Value) => True) _raw_i27 _raw_i28) → True := (by
                  intro _raw_i27 _raw_i28 h_6794 h_6799 _
                  let _value_i27 := Litex.semanticObject (M := M) _raw_i27 (M.member_isSet h_6794)
                  have h_6794 : Litex.In _value_i27 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) := h_6794
                  have h_6795 : Litex.In _value_i27 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i27 h_6794).1
                        )
                    )
                  have h_6796 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i27 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i27 h_6794).2.1
                        )
                    )
                  have h_6797 : Litex.Le _value_i27 _value_i17 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i27 h_6794).2.2
                        )
                    )
                  have h_6798 : Litex.In _value_i27 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i27 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6794)
                        )
                    )
                  let _value_i28 := Litex.semanticObject (M := M) _raw_i28 (M.member_isSet h_6799)
                  have h_6799 : Litex.In _value_i28 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) := h_6799
                  have h_6800 : Litex.In _value_i28 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i28 h_6799).1
                        )
                    )
                  have h_6801 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i28 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i28 h_6799).2.1
                        )
                    )
                  have h_6802 : Litex.Le _value_i28 _value_i17 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i28 h_6799).2.2
                        )
                    )
                  have h_6803 : Litex.In _value_i28 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i28 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_6799)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))))] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))))
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i27 : M.Value) (_raw_i28 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
              exact (Litex.inOfSame _value_i18 _value_i18 _object_h6516 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h6516
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                exact (show Litex.Same _left _right from rfl)) h_6516))))))
          let _object_w19 := (let _wd_1_0 := (Litex.R (M := M));
          let _wd_1_1 := (Litex.sub _value_i17 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToComplex _value_i17 (Litex.inNPos_natural _value_i17 h_6490)) (Litex.numberInC (M := M) (1 : ℂ)));
          let _wd_1_2 := _wd_1_1;
          (Litex.matrixSet _wd_1_0 _wd_1_1 _wd_1_2 (Litex.isSet _wd_1_0) (by
            let _atomic_wd_1_0 := _wd_1_2
            exact (Litex.integerToNaturalOfNonnegative _atomic_wd_1_0 (by
              let _atomic_wd_2_0 := _atomic_wd_1_0
              exact (Litex.subInZ _value_i17 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) (by
              let _atomic_wd_2_1 := _atomic_wd_1_0
              exact (Litex.integerPredecessorLe (Litex.number (M := M) (0 : ℂ)) _atomic_wd_2_1 (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490)) (Litex.sameRefl (Litex.number (M := M) 1)) h_6491)))) (by
            let _atomic_wd_1_0 := _wd_1_2
            exact (Litex.integerToNaturalOfNonnegative _atomic_wd_1_0 (by
              let _atomic_wd_2_0 := _atomic_wd_1_0
              exact (Litex.subInZ _value_i17 (Litex.number (M := M) (1 : ℂ)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))) (by
              let _atomic_wd_2_1 := _atomic_wd_1_0
              exact (Litex.integerPredecessorLe (Litex.number (M := M) (0 : ℂ)) _atomic_wd_2_1 (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490)) (Litex.sameRefl (Litex.number (M := M) 1)) h_6491))))))
          have h_6469 : (by
            let _atomic_wd_1_0 := _object_w18
            let _atomic_wd_1_1 := _object_w19
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w18
                    let _atomic_wd_1_1 := _object_w19
                    exact (show Litex.In _atomic_wd_1_0 _atomic_wd_1_1 from (let _litex_matrix := _atomic_wd_1_0; let _litex_matrix_signature := (Litex.matrixMinorSignature (_litex_matrix).val.order .real); Litex.inOfSame _litex_matrix _litex_matrix (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ((show @Eq M.Value _ _ from Eq.refl _)).symm (by rfl) (Litex.matrixMinorInRealFnSet _litex_matrix (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i33 : M.Value) (_raw_i34 : M.Value), M.mem _raw_i33 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490)))) → M.mem _raw_i34 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490)))) → ((fun (_raw_i33 : M.Value) (_raw_i34 : M.Value) => True) _raw_i33 _raw_i34) → True := (by
                          intro _raw_i33 _raw_i34 h_13066 h_13071 _
                          let _value_i33 := Litex.semanticObject (M := M) _raw_i33 (M.member_isSet h_13066)
                          have h_13066 : Litex.In _value_i33 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) := h_13066
                          have h_13067 : Litex.In _value_i33 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i33 h_13066).1
                                )
                            )
                          have h_13068 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i33 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i33 h_13066).2.1
                                )
                            )
                          have h_13069 : Litex.Le _value_i33 _value_i17 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i33 h_13066).2.2
                                )
                            )
                          have h_13070 : Litex.In _value_i33 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i33 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_13066)
                                )
                            )
                          let _value_i34 := Litex.semanticObject (M := M) _raw_i34 (M.member_isSet h_13071)
                          have h_13071 : Litex.In _value_i34 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) := h_13071
                          have h_13072 : Litex.In _value_i34 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i34 h_13071).1
                                )
                            )
                          have h_13073 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i34 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i34 h_13071).2.1
                                )
                            )
                          have h_13074 : Litex.Le _value_i34 _value_i17 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i34 h_13071).2.2
                                )
                            )
                          have h_13075 : Litex.In _value_i34 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))) _value_i34 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_13071)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i17 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i17 (Litex.inNPos_natural _value_i17 h_6490))))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i33 : M.Value) (_raw_i34 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                      exact (Litex.inOfSame _value_i18 _value_i18 _object_h6516 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h6516
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_6516))))))
                )
            )
          let _object_h13086 := (Litex.fnSet (Litex.matrixSignature _object_w19))
          have h_13086 : Litex.In _object_w18 _object_h13086 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _object_w18 _object_w18 _object_w19 _object_h13086 (Litex.sameRefl _object_w18) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet _object_w19)) h_6469)
                )
            )
          exact h_6469
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_minor_x5f_membership_x2f_statement_x2e_lit
