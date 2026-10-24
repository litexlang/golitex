import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_released_x5f_value_x5f_definitions_x2f_statement_x2e_lit

universe u v3 v4
variable {M : Litex.Semantics.{u}}

noncomputable def _object_i1 := (Litex.number (M := M) (2 : ℂ))
theorem h_3 : Litex.In (_object_i1 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
      )
  )
theorem h_4 : Litex.Same (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.number (M := M) (2 : ℂ)))
      )
  )

theorem h_5 : Litex.In (_object_i1 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (h_3 (M := M))
      )
  )

theorem h_6 : Litex.Same (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (h_4 (M := M))
      )
  )

noncomputable def _object_w4 := (Litex.add (_object_i1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ (h_3 (M := M))) (Litex.numberInC (M := M) (1 : ℂ)))

theorem h_7 : (by
  let _equal_wd_1_0 := (_object_w4 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (((congrArg₂ M.addValue (h_4 (M := M)) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))))).trans (((let _equal_wd_2_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
        (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) ((2 : ℂ) + (1 : ℂ)) (3 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num))))).trans ((Litex.sameRefl (Litex.number (M := M) (3 : ℂ)))).symm))
      )
  )

noncomputable def _object_i2 := (_object_w4 (M := M))
theorem h_100 : Litex.Same (_object_i2 (M := M)) (_object_w4 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_w4 (M := M)))
      )
  )

theorem h_101 : Litex.Same (_object_i2 (M := M)) (_object_w4 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (h_100 (M := M))
      )
  )

theorem h_102 : Litex.Same (_object_i2 (M := M)) (Litex.number (M := M) (3 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (((h_100 (M := M))).trans (h_7 (M := M)))
      )
  )

theorem h_104 : Litex.IsNonempty (Litex.R (M := M)) := (Litex.standardNonempty (M := M) Litex.StandardSetValue.real)

variable {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_105 : Litex.In _value_i3 (Litex.R (M := M)))

theorem h_106 {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_105 : Litex.In _value_i3 (Litex.R (M := M))) : Litex.In _value_i3 (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        h_105
      )
  )

theorem h_107 {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_105 : Litex.In _value_i3 (Litex.R (M := M))) : Litex.In _value_i3 (Litex.C (M := M)) :=
  (by
    litex_complete =>
      exact (
        (M.real_subset_complex _ h_105)
      )
  )

variable {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_131 : Litex.IsSet _value_i4)

theorem h_132 {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_105 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_131 : Litex.IsSet _value_i4) : Litex.IsSet _value_i4 :=
  (by
    litex_complete =>
      exact (
        h_131
      )
  )

theorem h_133 {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_105 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_131 : Litex.IsSet _value_i4) : Litex.IsSet _value_i4 :=
  (by
    litex_complete =>
      exact (
        h_131
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_released_x5f_value_x5f_definitions_x2f_statement_x2e_lit
