import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_cofactor_x5f_membership_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v7 v8 v9 v10
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_22 : Litex.In _value_i1 (Litex.NPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_47 : Litex.In _value_i2 (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) (Litex.inNPos_natural _value_i1 h_22) (Litex.inNPos_natural _value_i1 h_22))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_77 : Litex.In _value_i3 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22)))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_82 : Litex.In _value_i4 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22)))), (by
  let _object_w8 := (Litex.matrixCofactor _value_i2 _value_i1 _value_i3 _value_i4 h_22 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22)))
    exact h_77) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22)))
    exact h_82) (Litex.inNPos_natural _value_i1 h_22) (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) (Litex.inNPos_natural _value_i1 h_22) (Litex.inNPos_natural _value_i1 h_22))
    exact h_47))
  exact (by
    let _atomic_wd_1_0 := _object_w8
    exact Litex.In _atomic_wd_1_0 (Litex.C (M := M)))
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
          let _object_w8 := (Litex.matrixCofactor _value_i2 _value_i1 _value_i3 _value_i4 h_22 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22)))
            exact h_77) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i1 (Litex.inNPos_natural _value_i1 h_22)))
            exact h_82) (Litex.inNPos_natural _value_i1 h_22) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i1 _value_i1 (Litex.isSet (Litex.C (M := M))) (Litex.inNPos_natural _value_i1 h_22) (Litex.inNPos_natural _value_i1 h_22))
            exact h_47))
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w8
            exact Litex.In _atomic_wd_1_0 (Litex.C (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w8
                    exact (Litex.matrixCofactorInC _atomic_wd_1_0))
                )
            )
          exact h_1
        )
      )
  )

theorem h_199 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_219 : Litex.In _value_i7 (Litex.NPos (M := M))) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_244 : Litex.In _value_i8 (Litex.matrixSet (Litex.R (M := M)) _value_i7 _value_i7 (Litex.isSet (Litex.R (M := M))) (Litex.inNPos_natural _value_i7 h_219) (Litex.inNPos_natural _value_i7 h_219))) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_274 : Litex.In _value_i9 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219)))) {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_279 : Litex.In _value_i10 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219)))), (by
  let _object_h245 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i7 _value_i7 (Litex.isSet (Litex.R (M := M))) (Litex.inNPos_natural _value_i7 h_219) (Litex.inNPos_natural _value_i7 h_219))))
  have h_245 : Litex.In _value_i8 _object_h245 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i8 _value_i8 (Litex.matrixSet (Litex.R (M := M)) _value_i7 _value_i7 (Litex.isSet (Litex.R (M := M))) (Litex.inNPos_natural _value_i7 h_219) (Litex.inNPos_natural _value_i7 h_219)) _object_h245 (Litex.sameRefl _value_i8) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i7 _value_i7 (Litex.isSet (Litex.R (M := M))) (Litex.inNPos_natural _value_i7 h_219) (Litex.inNPos_natural _value_i7 h_219)))) h_244)
        )
    )
  let _object_w17 := (Litex.matrixCofactor _value_i8 _value_i7 _value_i9 _value_i10 h_219 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219)))
    exact h_274) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219)))
    exact h_279) (Litex.inNPos_natural _value_i7 h_219) (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i7 _value_i7 (Litex.isSet (Litex.C (M := M))) (Litex.inNPos_natural _value_i7 h_219) (Litex.inNPos_natural _value_i7 h_219))
    exact (show Litex.In _value_i8 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i17 : M.Value) (_raw_i18 : M.Value), M.mem _raw_i17 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219)))) → M.mem _raw_i18 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219)))) → ((fun (_raw_i17 : M.Value) (_raw_i18 : M.Value) => True) _raw_i17 _raw_i18) → True := (by
          intro _raw_i17 _raw_i18 h_523 h_528 _
          let _value_i17 := Litex.semanticObject (M := M) _raw_i17 (M.member_isSet h_523)
          have h_523 : Litex.In _value_i17 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) := h_523
          have h_524 : Litex.In _value_i17 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i17 h_523).1
                )
            )
          have h_525 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i17 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i17 h_523).2.1
                )
            )
          have h_526 : Litex.Le _value_i17 _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i17 h_523).2.2
                )
            )
          have h_527 : Litex.In _value_i17 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i17 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_523)
                )
            )
          let _value_i18 := Litex.semanticObject (M := M) _raw_i18 (M.member_isSet h_528)
          have h_528 : Litex.In _value_i18 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) := h_528
          have h_529 : Litex.In _value_i18 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i18 h_528).1
                )
            )
          have h_530 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i18 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i18 h_528).2.1
                )
            )
          have h_531 : Litex.Le _value_i18 _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i18 h_528).2.2
                )
            )
          have h_532 : Litex.In _value_i18 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i18 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_528)
                )
            )
          exact True.intro);
        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))))] (by
        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))))
        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) (_raw_i18 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
      exact (Litex.inOfSame _value_i8 _value_i8 _object_h245 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h245
        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
        exact (show Litex.Same _left _right from rfl)) h_245))))))
  exact (by
    let _atomic_wd_1_0 := _object_w17
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_219 _Host_i8 _rep_i8 _value_i8 h_244 _Host_i9 _rep_i9 _value_i9 h_274 _Host_i10 _rep_i10 _value_i10 h_279
          have h_220 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inNPos_positive _value_i7 h_219)
                )
            )
          have h_221 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i7 h_220)
                )
            )
          have h_222 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i7 h_220) _litex_zero.symm)
                )
            )
          let _object_h245 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.R (M := M)) _value_i7 _value_i7 (Litex.isSet (Litex.R (M := M))) (Litex.inNPos_natural _value_i7 h_219) (Litex.inNPos_natural _value_i7 h_219))))
          have h_245 : Litex.In _value_i8 _object_h245 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i8 _value_i8 (Litex.matrixSet (Litex.R (M := M)) _value_i7 _value_i7 (Litex.isSet (Litex.R (M := M))) (Litex.inNPos_natural _value_i7 h_219) (Litex.inNPos_natural _value_i7 h_219)) _object_h245 (Litex.sameRefl _value_i8) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.R (M := M)) _value_i7 _value_i7 (Litex.isSet (Litex.R (M := M))) (Litex.inNPos_natural _value_i7 h_219) (Litex.inNPos_natural _value_i7 h_219)))) h_244)
                )
            )
          have h_275 : Litex.In _value_i9 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i9 h_274).1
                )
            )
          have h_276 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i9 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i9 h_274).2.1
                )
            )
          have h_277 : Litex.Le _value_i9 _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i9 h_274).2.2
                )
            )
          have h_278 : Litex.In _value_i9 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i9 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_274)
                )
            )
          have h_280 : Litex.In _value_i10 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i10 h_279).1
                )
            )
          have h_281 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i10 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i10 h_279).2.1
                )
            )
          have h_282 : Litex.Le _value_i10 _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i10 h_279).2.2
                )
            )
          have h_283 : Litex.In _value_i10 (Litex.NPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i10 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_279)
                )
            )
          let _object_w17 := (Litex.matrixCofactor _value_i8 _value_i7 _value_i9 _value_i10 h_219 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219)))
            exact h_274) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219)))
            exact h_279) (Litex.inNPos_natural _value_i7 h_219) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) _value_i7 _value_i7 (Litex.isSet (Litex.C (M := M))) (Litex.inNPos_natural _value_i7 h_219) (Litex.inNPos_natural _value_i7 h_219))
            exact (show Litex.In _value_i8 _atomic_wd_1_1 from (Litex.functionRealToComplex (by
              let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i17 : M.Value) (_raw_i18 : M.Value), M.mem _raw_i17 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219)))) → M.mem _raw_i18 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219)))) → ((fun (_raw_i17 : M.Value) (_raw_i18 : M.Value) => True) _raw_i17 _raw_i18) → True := (by
                  intro _raw_i17 _raw_i18 h_523 h_528 _
                  let _value_i17 := Litex.semanticObject (M := M) _raw_i17 (M.member_isSet h_523)
                  have h_523 : Litex.In _value_i17 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) := h_523
                  have h_524 : Litex.In _value_i17 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i17 h_523).1
                        )
                    )
                  have h_525 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i17 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i17 h_523).2.1
                        )
                    )
                  have h_526 : Litex.Le _value_i17 _value_i7 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i17 h_523).2.2
                        )
                    )
                  have h_527 : Litex.In _value_i17 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i17 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_523)
                        )
                    )
                  let _value_i18 := Litex.semanticObject (M := M) _raw_i18 (M.member_isSet h_528)
                  have h_528 : Litex.In _value_i18 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) := h_528
                  have h_529 : Litex.In _value_i18 (Litex.Z (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i18 h_528).1
                        )
                    )
                  have h_530 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i18 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i18 h_528).2.1
                        )
                    )
                  have h_531 : Litex.Le _value_i18 _value_i7 :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i18 h_528).2.2
                        )
                    )
                  have h_532 : Litex.In _value_i18 (Litex.NPos (M := M)) :=
                    (by
                      litex_checked_step =>
                        exact (
                          (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i18 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_528)
                        )
                    )
                  exact True.intro);
                Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))))] (by
                have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))))
                have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))))
                exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
              )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) (_raw_i18 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
              exact (Litex.inOfSame _value_i8 _value_i8 _object_h245 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h245
                let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                exact (show Litex.Same _left _right from rfl)) h_245))))))
          have h_198 : (by
            let _atomic_wd_1_0 := _object_w17
            exact Litex.In _atomic_wd_1_0 (Litex.R (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w17
                    exact (show Litex.In _atomic_wd_1_0 (Litex.R (M := M)) from (Litex.matrixCofactorInR _atomic_wd_1_0 (by
                      let _atomic_wd_2_1 := (let _checked_header : ∀ (_raw_i19 : M.Value) (_raw_i20 : M.Value), M.mem _raw_i19 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219)))) → M.mem _raw_i20 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219)))) → ((fun (_raw_i19 : M.Value) (_raw_i20 : M.Value) => True) _raw_i19 _raw_i20) → True := (by
                          intro _raw_i19 _raw_i20 h_719 h_724 _
                          let _value_i19 := Litex.semanticObject (M := M) _raw_i19 (M.member_isSet h_719)
                          have h_719 : Litex.In _value_i19 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) := h_719
                          have h_720 : Litex.In _value_i19 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i19 h_719).1
                                )
                            )
                          have h_721 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i19 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i19 h_719).2.1
                                )
                            )
                          have h_722 : Litex.Le _value_i19 _value_i7 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i19 h_719).2.2
                                )
                            )
                          have h_723 : Litex.In _value_i19 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i19 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_719)
                                )
                            )
                          let _value_i20 := Litex.semanticObject (M := M) _raw_i20 (M.member_isSet h_724)
                          have h_724 : Litex.In _value_i20 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) := h_724
                          have h_725 : Litex.In _value_i20 (Litex.Z (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i20 h_724).1
                                )
                            )
                          have h_726 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i20 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i20 h_724).2.1
                                )
                            )
                          have h_727 : Litex.Le _value_i20 _value_i7 :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangeBounds (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i20 h_724).2.2
                                )
                            )
                          have h_728 : Litex.In _value_i20 (Litex.NPos (M := M)) :=
                            (by
                              litex_checked_step =>
                                exact (
                                  (Litex.inClosedRangePositive (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))) _value_i20 (1 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = ((1 : ℤ) : ℂ)))) (by norm_num) h_724)
                                )
                            )
                          exact True.intro);
                        Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))))] (by
                        have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))))
                        have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) _value_i7 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.naturalToInteger _value_i7 (Litex.inNPos_natural _value_i7 h_219))))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i19 : M.Value) (_raw_i20 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))))
                      exact (Litex.inOfSame _value_i8 _value_i8 _object_h245 _atomic_wd_2_1 (show @Eq M.Value _ _ from Eq.refl _) (by
                        let _left : Litex.Obj (M := M) (Litex.FunctionSignature M) := _object_h245
                        let _right : Litex.Obj (M := M) (Litex.FunctionSignature M) := _atomic_wd_2_1
                        exact (show Litex.Same _left _right from rfl)) h_245)))))
                )
            )
          exact h_198
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_cofactor_x5f_membership_x2f_statement_x2e_lit
