import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_sequence_x5f_spaces_x2f_statement_x2e_lit

universe u v1 v2 v4 v5
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

variable {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1)

theorem h_2 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) : Litex.IsNonempty (Litex.N (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.natural)

variable {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_3 : Litex.In _value_i2 (Litex.N (M := M)))

theorem h_4 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_3 : Litex.In _value_i2 (Litex.N (M := M))) : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
  (by
    litex_complete =>
      exact (
        (Litex.naturalNonnegative _value_i2 h_3)
      )
  )

noncomputable def _object_w3 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_3 : Litex.In _value_i2 (Litex.N (M := M))) := (Litex.finiteSeq _value_i1 _value_i2 h_1 h_3)

theorem h_5 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_3 : Litex.In _value_i2 (Litex.N (M := M))) : (by
  let _atomic_wd_1_0 := (_object_w3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_3)
  exact Litex.IsSet _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_3)
          exact (Litex.isSet _atomic_wd_1_0))
      )
  )

noncomputable def _object_i3 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_3 : Litex.In _value_i2 (Litex.N (M := M))) := (_object_w3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_3)
theorem h_18 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_3 : Litex.In _value_i2 (Litex.N (M := M))) : Litex.Same (_object_i3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_3) (_object_w3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_3) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_w3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_3))
      )
  )

theorem h_19 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_3 : Litex.In _value_i2 (Litex.N (M := M))) : (by
  let _equal_wd_1_1 := (_object_w3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_3)
  exact Litex.Same (_object_i3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_3) _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (h_18 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_3)
      )
  )

noncomputable def _object_w4 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_3 : Litex.In _value_i2 (Litex.N (M := M))) := (Litex.finiteSeq (_object_i3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_3) (Litex.number (M := M) (0 : ℂ)) (Litex.isSetOfSame (_object_w3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_3) (_object_i3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_3) ((h_18 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_3)).symm (h_5 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_3)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num)))

theorem h_21 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_3 : Litex.In _value_i2 (Litex.N (M := M))) : (by
  let _atomic_wd_1_0 := (_object_w4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_3)
  exact Litex.IsSet _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w4 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_3)
          exact (Litex.isSet _atomic_wd_1_0))
      )
  )

theorem h_39 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_3 : Litex.In _value_i2 (Litex.N (M := M))) : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_53 : Litex.IsSet _value_i4) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_54 : Litex.In _value_i5 (Litex.N (M := M))), (by
  let _object_w5 := (Litex.finiteSeq _value_i4 _value_i5 h_53 h_54)
  exact (by
    let _atomic_wd_1_0 := _object_w5
    exact Litex.IsSet _atomic_wd_1_0)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_53 _Host_i5 _rep_i5 _value_i5 h_54
          have h_55 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _value_i5 h_54)
                )
            )
          let _object_w5 := (Litex.finiteSeq _value_i4 _value_i5 h_53 h_54)
          have h_38 : (by
            let _atomic_wd_1_0 := _object_w5
            exact Litex.IsSet _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w5
                    exact (Litex.isSet _atomic_wd_1_0))
                )
            )
          exact h_38
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_sequence_x5f_spaces_x2f_statement_x2e_lit
