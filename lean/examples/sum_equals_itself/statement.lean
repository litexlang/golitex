import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_sum_x5f_equals_x5f_itself_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_27 : Litex.In _value_i1 (Litex.C (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_28 : Litex.In _value_i2 (Litex.C (M := M))), (by
  let _object_w2 := (Litex.add _value_i1 _value_i2 h_27 h_28)
  exact (by
    let _equal_wd_1_0 := _object_w2
    let _equal_wd_1_1 := _equal_wd_1_0
    exact Litex.Same _equal_wd_1_1 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_27 _Host_i2 _rep_i2 _value_i2 h_28
          let _object_w2 := (Litex.add _value_i1 _value_i2 h_27 h_28)
          have h_1 : (by
            let _equal_wd_1_0 := _object_w2
            let _equal_wd_1_1 := _equal_wd_1_0
            exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show @Eq M.Value _ _ from Eq.refl _)
                )
            )
          exact h_1
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_sum_x5f_equals_x5f_itself_x2f_statement_x2e_lit
