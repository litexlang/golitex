import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_template_x5f_carrier_x5f_copy_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

noncomputable def _template_i2 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) : Litex.Obj (M := M) M.Value := by
  let _object_i2 := _value_i1
  have h_6 : Litex.IsSet _object_i2 :=
    (by
      litex_checked_step =>
        exact (
          h_1
        )
    )
  have h_7 : Litex.Same _object_i2 _value_i1 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.sameRefl _value_i1)
        )
    )
  exact Litex.semanticObject (Litex.denote _object_i2) (Litex.isSet _object_i2)

theorem h_9 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1), Litex.IsSet ((_template_i2 (M := M)) _value_i1 h_1) := by
  intro _Host_i1 _rep_i1 _value_i1 h_1
  let _object_i2 := _value_i1
  have h_6 : Litex.IsSet _object_i2 :=
    (by
      litex_checked_step =>
        exact (
          h_1
        )
    )
  have h_7 : Litex.Same _object_i2 _value_i1 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.sameRefl _value_i1)
        )
    )
  exact h_6

theorem h_11 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1), Litex.Same ((_template_i2 (M := M)) _value_i1 h_1) _value_i1 := by
  intro _Host_i1 _rep_i1 _value_i1 h_1
  let _object_i2 := _value_i1
  have h_6 : Litex.IsSet _object_i2 :=
    (by
      litex_checked_step =>
        exact (
          h_1
        )
    )
  have h_7 : Litex.Same _object_i2 _value_i1 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.sameRefl _value_i1)
        )
    )
  exact h_7

noncomputable def _object_w1 := ((_template_i2 (M := M)) (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))

theorem h_12 : (by
  let _equal_wd_1_0 := (_object_w1 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.R (M := M))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w1 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.R (M := M)) from (show (Litex.denote _equal_wd_1_0) = (Litex.denote (Litex.R (M := M))) from (show @Eq M.Value _ _ from Eq.refl _))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_template_x5f_carrier_x5f_copy_x2f_statement_x2e_lit
