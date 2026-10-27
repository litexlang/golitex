import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_intersection_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_3 : Litex.IsFiniteSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_4 : Litex.IsFiniteSet _value_i2), (by
  let _object_w1 := (Litex.intersect _value_i1 _value_i2)
  exact (by
    let _atomic_wd_1_0 := _object_w1
    exact Litex.IsFiniteSet _atomic_wd_1_0)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_3 _Host_i2 _rep_i2 _value_i2 h_4
          let _object_w1 := (Litex.intersect _value_i1 _value_i2)
          have h_1 : (by
            let _atomic_wd_1_0 := _object_w1
            exact Litex.IsFiniteSet _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w1
                    exact (Litex.finiteSetIntersect _atomic_wd_1_0 h_3 h_4))
                )
            )
          exact h_1
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_intersection_x2f_statement_x2e_lit
