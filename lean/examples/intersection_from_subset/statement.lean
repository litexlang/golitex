import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_intersection_x5f_from_x5f_subset_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_5 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_6 : Litex.IsSet _value_i2) (h_1 : Litex.Subset _value_i1 _value_i2), (by
  let _object_w1 := (Litex.intersect _value_i1 _value_i2)
  let _object_w2 := (Litex.intersect _value_i2 _value_i1)
  exact (((by
    let _equal_wd_1_0 := _object_w1
    exact Litex.Same _equal_wd_1_0 _value_i1)) ∧ ((by
    let _equal_wd_1_0 := _object_w2
    exact Litex.Same _equal_wd_1_0 _value_i1)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_5 _Host_i2 _rep_i2 _value_i2 h_6 h_1
          let _object_w1 := (Litex.intersect _value_i1 _value_i2)
          have h_2 : (by
            let _equal_wd_1_0 := _object_w1
            exact Litex.Same _equal_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w1;
                  (show Litex.Same _equal_wd_1_0 _value_i1 from (let _litex_set := _equal_wd_1_0; (Litex.intersectOfSubsetLeft _litex_set.val.left _litex_set.val.right h_1))))
                )
            )
          let _object_w2 := (Litex.intersect _value_i2 _value_i1)
          have h_3 : (by
            let _equal_wd_1_0 := _object_w2
            exact Litex.Same _equal_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w2;
                  (show Litex.Same _equal_wd_1_0 _value_i1 from (let _litex_set := _equal_wd_1_0; (Litex.intersectOfSubsetRight _litex_set.val.left _litex_set.val.right h_1))))
                )
            )
          exact (And.intro h_2 h_3)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_intersection_x5f_from_x5f_subset_x2f_statement_x2e_lit
