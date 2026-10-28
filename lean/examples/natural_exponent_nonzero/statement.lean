import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_natural_x5f_exponent_x5f_nonzero_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_1 : Litex.IsNonempty (Litex.N (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.natural)

variable {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.N (M := M)))

theorem h_3 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.N (M := M))) : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
  (by
    litex_complete =>
      exact (
        (Litex.naturalNonnegative _value_i1 h_2)
      )
  )

noncomputable def _object_w3 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.N (M := M))) := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) _value_i1 (Litex.NativeBridge.asNat _value_i1 h_2) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) h_2 (Litex.NativeBridge.asNat_spec _value_i1 h_2))

theorem h_4 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.N (M := M))) : (by
  let _atomic_wd_1_0 := (_object_w3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)
  exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w3 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2)
          exact (fun _litex_equal => (Litex.powNonzeroOfBase _atomic_wd_1_0 (Litex.naturalToInteger _value_i1 h_2) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
      )
  )

theorem h_35 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.N (M := M))) : Litex.IsNonempty (Litex.NPos (M := M)) := (Litex.nPosNonempty (M := M))

variable {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_36 : Litex.In _value_i2 (Litex.NPos (M := M)))

theorem h_37 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_36 : Litex.In _value_i2 (Litex.NPos (M := M))) : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
  (by
    litex_complete =>
      exact (
        (Litex.inNPos_positive _value_i2 h_36)
      )
  )

theorem h_38 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_36 : Litex.In _value_i2 (Litex.NPos (M := M))) : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
  (by
    litex_complete =>
      exact (
        (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 (h_37 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_36))
      )
  )

theorem h_39 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_36 : Litex.In _value_i2 (Litex.NPos (M := M))) : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 (h_37 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_36)) _litex_zero.symm)
      )
  )

noncomputable def _object_w5 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_36 : Litex.In _value_i2 (Litex.NPos (M := M))) := (Litex.powNatReal (Litex.number (M := M) (2 : ℂ)) _value_i2 (Litex.NativeBridge.asNat _value_i2 (Litex.inNPos_natural _value_i2 h_36)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.inNPos_natural _value_i2 h_36) (Litex.NativeBridge.asNat_spec _value_i2 (Litex.inNPos_natural _value_i2 h_36)))

theorem h_40 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.N (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_36 : Litex.In _value_i2 (Litex.NPos (M := M))) : (by
  let _atomic_wd_1_1 := (_object_w5 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_36)
  exact ¬ Litex.Same (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_1 := (_object_w5 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_2 (_Host_i2 := _Host_i2) (_rep_i2 := _rep_i2) _value_i2 h_36)
          exact (fun _litex_equal => (Litex.powNonzeroOfBase _atomic_wd_1_1 (Litex.naturalToInteger _value_i2 (Litex.inNPos_natural _value_i2 h_36)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) ((_litex_equal.symm).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_natural_x5f_exponent_x5f_nonzero_x2f_statement_x2e_lit
