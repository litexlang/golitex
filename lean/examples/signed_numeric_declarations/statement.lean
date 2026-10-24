import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_signed_x5f_numeric_x5f_declarations_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6 v7 v8
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_1 : Litex.IsNonempty (Litex.QPos (M := M)) := (Litex.qPosNonempty (M := M))

variable {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M)))

theorem h_3 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
  (by
    litex_complete =>
      exact (
        (Litex.inQPos_positive _value_i1 h_2)
      )
  )

theorem h_4 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
  (by
    litex_complete =>
      exact (
        (Litex.ltToLe (Litex.number (M := M) 0) _value_i1 (h_3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))
      )
  )

theorem h_5 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i1 (h_3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)) _litex_zero.symm)
      )
  )

noncomputable def _object_w3 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) := (Litex.div _value_i1 _value_i1 (Litex.rationalToComplex _value_i1 (Litex.inQPos_base _value_i1 h_2)) (Litex.rationalToComplex _value_i1 (Litex.inQPos_base _value_i1 h_2)) (h_5 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2))

theorem h_6 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) : (by
  let _equal_wd_1_0 := (_object_w3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2);
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i1 (Litex.rationalToComplex _value_i1 (Litex.inQPos_base _value_i1 h_2))) / (Litex.NativeBridge.asComplex _value_i1 (Litex.rationalToComplex _value_i1 (Litex.inQPos_base _value_i1 h_2)))) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i1 _value_i1 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.rationalToComplex _value_i1 (Litex.inQPos_base _value_i1 h_2))) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.rationalToComplex _value_i1 (Litex.inQPos_base _value_i1 h_2)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
          have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i1 (Litex.rationalToComplex _value_i1 (Litex.inQPos_base _value_i1 h_2))) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i1 (Litex.NativeBridge.asComplex _value_i1 (Litex.rationalToComplex _value_i1 (Litex.inQPos_base _value_i1 h_2))) (Litex.NativeBridge.asComplex_spec _value_i1 (Litex.rationalToComplex _value_i1 (Litex.inQPos_base _value_i1 h_2))) (h_5 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)
          litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
        ))))
      )
  )

theorem h_190 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) : Litex.IsNonempty (Litex.QNeg (M := M)) := (Litex.qNegNonempty (M := M))

variable {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M)))

theorem h_192 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) : Litex.Lt _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inQNeg_negative _value_i2 h_191)
      )
  )

theorem h_193 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) : Litex.Le _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.ltToLe _value_i2 (Litex.number (M := M) 0) (h_192 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191))
      )
  )

theorem h_194 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.ltNotSame _value_i2 (Litex.number (M := M) 0) (h_192 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191))
      )
  )

noncomputable def _object_w6 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) := (Litex.div _value_i2 _value_i2 (Litex.rationalToComplex _value_i2 (Litex.inQNeg_base _value_i2 h_191)) (Litex.rationalToComplex _value_i2 (Litex.inQNeg_base _value_i2 h_191)) (h_194 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191))

theorem h_195 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) : (by
  let _equal_wd_1_0 := (_object_w6 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w6 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191);
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i2 (Litex.rationalToComplex _value_i2 (Litex.inQNeg_base _value_i2 h_191))) / (Litex.NativeBridge.asComplex _value_i2 (Litex.rationalToComplex _value_i2 (Litex.inQNeg_base _value_i2 h_191)))) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i2 _value_i2 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.rationalToComplex _value_i2 (Litex.inQNeg_base _value_i2 h_191))) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.rationalToComplex _value_i2 (Litex.inQNeg_base _value_i2 h_191)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
          have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i2 (Litex.rationalToComplex _value_i2 (Litex.inQNeg_base _value_i2 h_191))) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i2 (Litex.NativeBridge.asComplex _value_i2 (Litex.rationalToComplex _value_i2 (Litex.inQNeg_base _value_i2 h_191))) (Litex.NativeBridge.asComplex_spec _value_i2 (Litex.rationalToComplex _value_i2 (Litex.inQNeg_base _value_i2 h_191))) (h_194 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191)
          litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
        ))))
      )
  )

theorem h_432 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) : Litex.IsNonempty (Litex.ZNeg (M := M)) := (Litex.zNegNonempty (M := M))

variable {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M)))

theorem h_434 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M))) : Litex.Lt _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inZNeg_negative _value_i3 h_433)
      )
  )

theorem h_435 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M))) : Litex.Le _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.ltToLe _value_i3 (Litex.number (M := M) 0) (h_434 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433))
      )
  )

theorem h_436 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M))) : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.ltNotSame _value_i3 (Litex.number (M := M) 0) (h_434 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433))
      )
  )

noncomputable def _object_w8 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M))) := (Litex.div _value_i3 _value_i3 (Litex.integerToComplex _value_i3 (Litex.inZNeg_base _value_i3 h_433)) (Litex.integerToComplex _value_i3 (Litex.inZNeg_base _value_i3 h_433)) (h_436 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433))

theorem h_437 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M))) : (by
  let _equal_wd_1_0 := (_object_w8 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w8 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433);
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i3 (Litex.integerToComplex _value_i3 (Litex.inZNeg_base _value_i3 h_433))) / (Litex.NativeBridge.asComplex _value_i3 (Litex.integerToComplex _value_i3 (Litex.inZNeg_base _value_i3 h_433)))) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i3 _value_i3 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.integerToComplex _value_i3 (Litex.inZNeg_base _value_i3 h_433))) (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.integerToComplex _value_i3 (Litex.inZNeg_base _value_i3 h_433)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
          have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i3 (Litex.integerToComplex _value_i3 (Litex.inZNeg_base _value_i3 h_433))) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i3 (Litex.NativeBridge.asComplex _value_i3 (Litex.integerToComplex _value_i3 (Litex.inZNeg_base _value_i3 h_433))) (Litex.NativeBridge.asComplex_spec _value_i3 (Litex.integerToComplex _value_i3 (Litex.inZNeg_base _value_i3 h_433))) (h_436 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433)
          litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
        ))))
      )
  )

theorem h_735 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M))) : Litex.IsNonempty (Litex.RNeg (M := M)) := (Litex.rNegNonempty (M := M))

variable {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_736 : Litex.In _value_i4 (Litex.RNeg (M := M)))

theorem h_737 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_736 : Litex.In _value_i4 (Litex.RNeg (M := M))) : Litex.Lt _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inRNeg_negative _value_i4 h_736)
      )
  )

theorem h_738 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_736 : Litex.In _value_i4 (Litex.RNeg (M := M))) : Litex.Le _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.ltToLe _value_i4 (Litex.number (M := M) 0) (h_737 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433 (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_736))
      )
  )

theorem h_739 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_736 : Litex.In _value_i4 (Litex.RNeg (M := M))) : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.ltNotSame _value_i4 (Litex.number (M := M) 0) (h_737 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433 (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_736))
      )
  )

noncomputable def _object_w10 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_736 : Litex.In _value_i4 (Litex.RNeg (M := M))) := (Litex.div _value_i4 _value_i4 (Litex.realToComplex _value_i4 (Litex.inRNeg_base _value_i4 h_736)) (Litex.realToComplex _value_i4 (Litex.inRNeg_base _value_i4 h_736)) (h_739 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433 (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_736))

theorem h_740 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_736 : Litex.In _value_i4 (Litex.RNeg (M := M))) : (by
  let _equal_wd_1_0 := (_object_w10 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433 (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_736)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w10 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433 (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_736);
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 (Litex.inRNeg_base _value_i4 h_736))) / (Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 (Litex.inRNeg_base _value_i4 h_736)))) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i4 _value_i4 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.realToComplex _value_i4 (Litex.inRNeg_base _value_i4 h_736))) (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.realToComplex _value_i4 (Litex.inRNeg_base _value_i4 h_736)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
          have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 (Litex.inRNeg_base _value_i4 h_736))) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i4 (Litex.NativeBridge.asComplex _value_i4 (Litex.realToComplex _value_i4 (Litex.inRNeg_base _value_i4 h_736))) (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.realToComplex _value_i4 (Litex.inRNeg_base _value_i4 h_736))) (h_739 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433 (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_736)
          litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
        ))))
      )
  )

theorem h_1043 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_736 : Litex.In _value_i4 (Litex.RNeg (M := M))) : Litex.IsNonempty (Litex.QStar (M := M)) := (Litex.qStarNonempty (M := M))

variable {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_1044 : Litex.In _value_i5 (Litex.QStar (M := M)))

theorem h_1045 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_736 : Litex.In _value_i4 (Litex.RNeg (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_1044 : Litex.In _value_i5 (Litex.QStar (M := M))) : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inQStar_nonzero _value_i5 h_1044)
      )
  )

noncomputable def _object_w12 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_736 : Litex.In _value_i4 (Litex.RNeg (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_1044 : Litex.In _value_i5 (Litex.QStar (M := M))) := (Litex.div _value_i5 _value_i5 (Litex.rationalToComplex _value_i5 (Litex.inQStar_base _value_i5 h_1044)) (Litex.rationalToComplex _value_i5 (Litex.inQStar_base _value_i5 h_1044)) (h_1045 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433 (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_736 (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_1044))

theorem h_1046 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_736 : Litex.In _value_i4 (Litex.RNeg (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_1044 : Litex.In _value_i5 (Litex.QStar (M := M))) : (by
  let _equal_wd_1_0 := (_object_w12 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433 (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_736 (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_1044)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w12 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433 (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_736 (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_1044);
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i5 (Litex.rationalToComplex _value_i5 (Litex.inQStar_base _value_i5 h_1044))) / (Litex.NativeBridge.asComplex _value_i5 (Litex.rationalToComplex _value_i5 (Litex.inQStar_base _value_i5 h_1044)))) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i5 _value_i5 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.rationalToComplex _value_i5 (Litex.inQStar_base _value_i5 h_1044))) (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.rationalToComplex _value_i5 (Litex.inQStar_base _value_i5 h_1044)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
          have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i5 (Litex.rationalToComplex _value_i5 (Litex.inQStar_base _value_i5 h_1044))) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i5 (Litex.NativeBridge.asComplex _value_i5 (Litex.rationalToComplex _value_i5 (Litex.inQStar_base _value_i5 h_1044))) (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.rationalToComplex _value_i5 (Litex.inQStar_base _value_i5 h_1044))) (h_1045 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433 (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_736 (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_1044)
          litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
        ))))
      )
  )

theorem h_1401 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_736 : Litex.In _value_i4 (Litex.RNeg (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_1044 : Litex.In _value_i5 (Litex.QStar (M := M))) : Litex.IsNonempty (Litex.ZStar (M := M)) := (Litex.zStarNonempty (M := M))

variable {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_1402 : Litex.In _value_i6 (Litex.ZStar (M := M)))

theorem h_1403 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_736 : Litex.In _value_i4 (Litex.RNeg (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_1044 : Litex.In _value_i5 (Litex.QStar (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_1402 : Litex.In _value_i6 (Litex.ZStar (M := M))) : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inZStar_nonzero _value_i6 h_1402)
      )
  )

noncomputable def _object_w14 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_736 : Litex.In _value_i4 (Litex.RNeg (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_1044 : Litex.In _value_i5 (Litex.QStar (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_1402 : Litex.In _value_i6 (Litex.ZStar (M := M))) := (Litex.div _value_i6 _value_i6 (Litex.integerToComplex _value_i6 (Litex.inZStar_base _value_i6 h_1402)) (Litex.integerToComplex _value_i6 (Litex.inZStar_base _value_i6 h_1402)) (h_1403 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433 (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_736 (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_1044 (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_1402))

theorem h_1404 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_736 : Litex.In _value_i4 (Litex.RNeg (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_1044 : Litex.In _value_i5 (Litex.QStar (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_1402 : Litex.In _value_i6 (Litex.ZStar (M := M))) : (by
  let _equal_wd_1_0 := (_object_w14 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433 (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_736 (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_1044 (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_1402)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w14 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433 (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_736 (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_1044 (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_1402);
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i6 (Litex.integerToComplex _value_i6 (Litex.inZStar_base _value_i6 h_1402))) / (Litex.NativeBridge.asComplex _value_i6 (Litex.integerToComplex _value_i6 (Litex.inZStar_base _value_i6 h_1402)))) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i6 _value_i6 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.integerToComplex _value_i6 (Litex.inZStar_base _value_i6 h_1402))) (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.integerToComplex _value_i6 (Litex.inZStar_base _value_i6 h_1402)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
          have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i6 (Litex.integerToComplex _value_i6 (Litex.inZStar_base _value_i6 h_1402))) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i6 (Litex.NativeBridge.asComplex _value_i6 (Litex.integerToComplex _value_i6 (Litex.inZStar_base _value_i6 h_1402))) (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.integerToComplex _value_i6 (Litex.inZStar_base _value_i6 h_1402))) (h_1403 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433 (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_736 (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_1044 (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_1402)
          litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
        ))))
      )
  )

theorem h_1827 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_736 : Litex.In _value_i4 (Litex.RNeg (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_1044 : Litex.In _value_i5 (Litex.QStar (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_1402 : Litex.In _value_i6 (Litex.ZStar (M := M))) : Litex.IsNonempty (Litex.RStar (M := M)) := (Litex.rStarNonempty (M := M))

variable {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_1828 : Litex.In _value_i7 (Litex.RStar (M := M)))

theorem h_1829 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_736 : Litex.In _value_i4 (Litex.RNeg (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_1044 : Litex.In _value_i5 (Litex.QStar (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_1402 : Litex.In _value_i6 (Litex.ZStar (M := M))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_1828 : Litex.In _value_i7 (Litex.RStar (M := M))) : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inRStar_nonzero _value_i7 h_1828)
      )
  )

noncomputable def _object_w16 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_736 : Litex.In _value_i4 (Litex.RNeg (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_1044 : Litex.In _value_i5 (Litex.QStar (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_1402 : Litex.In _value_i6 (Litex.ZStar (M := M))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_1828 : Litex.In _value_i7 (Litex.RStar (M := M))) := (Litex.div _value_i7 _value_i7 (Litex.realToComplex _value_i7 (Litex.inRStar_base _value_i7 h_1828)) (Litex.realToComplex _value_i7 (Litex.inRStar_base _value_i7 h_1828)) (h_1829 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433 (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_736 (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_1044 (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_1402 (_Host_i7 := _Host_i7) (_rep_i7 := _rep_i7) _value_i7 h_1828))

theorem h_1830 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_736 : Litex.In _value_i4 (Litex.RNeg (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_1044 : Litex.In _value_i5 (Litex.QStar (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_1402 : Litex.In _value_i6 (Litex.ZStar (M := M))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_1828 : Litex.In _value_i7 (Litex.RStar (M := M))) : (by
  let _equal_wd_1_0 := (_object_w16 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433 (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_736 (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_1044 (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_1402 (_Host_i7 := _Host_i7) (_rep_i7 := _rep_i7) _value_i7 h_1828)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w16 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433 (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_736 (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_1044 (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_1402 (_Host_i7 := _Host_i7) (_rep_i7 := _rep_i7) _value_i7 h_1828);
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i7 (Litex.realToComplex _value_i7 (Litex.inRStar_base _value_i7 h_1828))) / (Litex.NativeBridge.asComplex _value_i7 (Litex.realToComplex _value_i7 (Litex.inRStar_base _value_i7 h_1828)))) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i7 _value_i7 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.realToComplex _value_i7 (Litex.inRStar_base _value_i7 h_1828))) (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.realToComplex _value_i7 (Litex.inRStar_base _value_i7 h_1828)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
          have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i7 (Litex.realToComplex _value_i7 (Litex.inRStar_base _value_i7 h_1828))) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i7 (Litex.NativeBridge.asComplex _value_i7 (Litex.realToComplex _value_i7 (Litex.inRStar_base _value_i7 h_1828))) (Litex.NativeBridge.asComplex_spec _value_i7 (Litex.realToComplex _value_i7 (Litex.inRStar_base _value_i7 h_1828))) (h_1829 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433 (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_736 (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_1044 (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_1402 (_Host_i7 := _Host_i7) (_rep_i7 := _rep_i7) _value_i7 h_1828)
          litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
        ))))
      )
  )

theorem h_2249 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_736 : Litex.In _value_i4 (Litex.RNeg (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_1044 : Litex.In _value_i5 (Litex.QStar (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_1402 : Litex.In _value_i6 (Litex.ZStar (M := M))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_1828 : Litex.In _value_i7 (Litex.RStar (M := M))) : Litex.IsNonempty (Litex.CStar (M := M)) := (Litex.cStarNonempty (M := M))

variable {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_2250 : Litex.In _value_i8 (Litex.CStar (M := M)))

theorem h_2251 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_736 : Litex.In _value_i4 (Litex.RNeg (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_1044 : Litex.In _value_i5 (Litex.QStar (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_1402 : Litex.In _value_i6 (Litex.ZStar (M := M))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_1828 : Litex.In _value_i7 (Litex.RStar (M := M))) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_2250 : Litex.In _value_i8 (Litex.CStar (M := M))) : ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inCStar_nonzero _value_i8 h_2250)
      )
  )

noncomputable def _object_w18 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_736 : Litex.In _value_i4 (Litex.RNeg (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_1044 : Litex.In _value_i5 (Litex.QStar (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_1402 : Litex.In _value_i6 (Litex.ZStar (M := M))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_1828 : Litex.In _value_i7 (Litex.RStar (M := M))) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_2250 : Litex.In _value_i8 (Litex.CStar (M := M))) := (Litex.div _value_i8 _value_i8 (Litex.inCStar_base _value_i8 h_2250) (Litex.inCStar_base _value_i8 h_2250) (h_2251 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433 (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_736 (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_1044 (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_1402 (_Host_i7 := _Host_i7) (_rep_i7 := _rep_i7) _value_i7 h_1828 (_Host_i8 := _Host_i8) (_rep_i8 := _rep_i8) _value_i8 h_2250))

theorem h_2252 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.QPos (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_191 : Litex.In _value_i2 (Litex.QNeg (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_433 : Litex.In _value_i3 (Litex.ZNeg (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_736 : Litex.In _value_i4 (Litex.RNeg (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_1044 : Litex.In _value_i5 (Litex.QStar (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_1402 : Litex.In _value_i6 (Litex.ZStar (M := M))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_1828 : Litex.In _value_i7 (Litex.RStar (M := M))) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_2250 : Litex.In _value_i8 (Litex.CStar (M := M))) : (by
  let _equal_wd_1_0 := (_object_w18 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433 (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_736 (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_1044 (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_1402 (_Host_i7 := _Host_i7) (_rep_i7 := _rep_i7) _value_i7 h_1828 (_Host_i8 := _Host_i8) (_rep_i8 := _rep_i8) _value_i8 h_2250)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w18 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433 (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_736 (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_1044 (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_1402 (_Host_i7 := _Host_i7) (_rep_i7 := _rep_i7) _value_i7 h_1828 (_Host_i8 := _Host_i8) (_rep_i8 := _rep_i8) _value_i8 h_2250);
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i8 (Litex.inCStar_base _value_i8 h_2250)) / (Litex.NativeBridge.asComplex _value_i8 (Litex.inCStar_base _value_i8 h_2250))) (1 : ℂ) (Litex.NativeBridge.denoteDiv _value_i8 _value_i8 (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.inCStar_base _value_i8 h_2250)) (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.inCStar_base _value_i8 h_2250))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by
          have _litex_nz_0 : ((Litex.NativeBridge.asComplex _value_i8 (Litex.inCStar_base _value_i8 h_2250)) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote _value_i8 (Litex.NativeBridge.asComplex _value_i8 (Litex.inCStar_base _value_i8 h_2250)) (Litex.NativeBridge.asComplex_spec _value_i8 (Litex.inCStar_base _value_i8 h_2250)) (h_2251 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_191 (_Host_i3 := _Host_i3) (_rep_i3 := _rep_i3) _value_i3 h_433 (_Host_i4 := _Host_i4) (_rep_i4 := _rep_i4) _value_i4 h_736 (_Host_i5 := _Host_i5) (_rep_i5 := _rep_i5) _value_i5 h_1044 (_Host_i6 := _Host_i6) (_rep_i6 := _rep_i6) _value_i6 h_1402 (_Host_i7 := _Host_i7) (_rep_i7 := _rep_i7) _value_i7 h_1828 (_Host_i8 := _Host_i8) (_rep_i8 := _rep_i8) _value_i8 h_2250)
          litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
        ))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_signed_x5f_numeric_x5f_declarations_x2f_statement_x2e_lit
