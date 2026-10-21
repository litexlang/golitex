import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_zero_x5f_difference_x5f_equality_x2f_statement_x2e_lit

universe u v1 v2 v3 v4
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.C (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_17 : Litex.In _value_i2 (Litex.C (M := M))) (h_1 : Litex.Same (Litex.sub _value_i1 _value_i2 h_16 h_17) (Litex.number (M := M) (0 : ℂ))), Litex.Same _value_i1 _value_i2 :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 h_16 _Host_i2 _rep_i2 _value_i2 h_17 h_1
    have h_2 : Litex.Same _value_i1 _value_i2 :=
      (by
        let _litex_difference := (Litex.sub _value_i1 _value_i2 h_16 h_17)
        have _litex_zero : Litex.Same _litex_difference (Litex.number (M := M) 0) := h_1
        have _litex_same := Litex.sameOfSubZero _litex_difference.val.left _litex_difference.val.right _litex_difference.wd.1 _litex_difference.wd.2 _litex_zero
        exact _litex_same
      )
    exact h_2
  )

theorem h_34 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_48 : Litex.In _value_i3 (Litex.C (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_49 : Litex.In _value_i4 (Litex.C (M := M))) (h_32 : Litex.Same (Litex.number (M := M) (0 : ℂ)) (Litex.sub _value_i4 _value_i3 h_49 h_48)), Litex.Same _value_i3 _value_i4 :=
  (by
    intro _Host_i3 _rep_i3 _value_i3 h_48 _Host_i4 _rep_i4 _value_i4 h_49 h_32
    have h_33 : Litex.Same _value_i3 _value_i4 :=
      (by
        let _litex_difference := (Litex.sub _value_i4 _value_i3 h_49 h_48)
        have _litex_zero : Litex.Same _litex_difference (Litex.number (M := M) 0) := (h_32).symm
        have _litex_same := Litex.sameOfSubZero _litex_difference.val.left _litex_difference.val.right _litex_difference.wd.1 _litex_difference.wd.2 _litex_zero
        exact _litex_same.symm
      )
    exact h_33
  )
end LitexCompiled.file_lean_x2f_examples_x2f_zero_x5f_difference_x5f_equality_x2f_statement_x2e_lit
