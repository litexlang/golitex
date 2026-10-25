import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_intersection_x5f_distributes_x5f_over_x5f_union_x2f_statement_x2e_lit

universe u v1 v2 v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_3 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_4 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_5 : Litex.IsSet _value_i3), (by
  let _object_w1 := (let _wd_1_0 := _value_i1;
  let _wd_1_1 := (Litex.union _value_i2 _value_i3);
  (Litex.intersect _wd_1_0 _wd_1_1))
  let _object_w2 := (let _wd_1_0 := (Litex.intersect _value_i1 _value_i2);
  let _wd_1_1 := (Litex.intersect _value_i1 _value_i3);
  (Litex.union _wd_1_0 _wd_1_1))
  exact (by
    let _equal_wd_1_0 := _object_w1
    let _equal_wd_1_1 := _object_w2
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_3 _Host_i2 _rep_i2 _value_i2 h_4 _Host_i3 _rep_i3 _value_i3 h_5
          let _object_w1 := (let _wd_1_0 := _value_i1;
          let _wd_1_1 := (Litex.union _value_i2 _value_i3);
          (Litex.intersect _wd_1_0 _wd_1_1))
          let _object_w2 := (let _wd_1_0 := (Litex.intersect _value_i1 _value_i2);
          let _wd_1_1 := (Litex.intersect _value_i1 _value_i3);
          (Litex.union _wd_1_0 _wd_1_1))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w1
            let _equal_wd_1_1 := _object_w2
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w1;
                  let _equal_wd_1_1 := _object_w2;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (let _litex_set := _equal_wd_1_0; (Litex.intersectUnionDistrib _litex_set.val.left _litex_set.val.right.val.left _litex_set.val.right.val.right))))
                )
            )
          exact h_1
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_intersection_x5f_distributes_x5f_over_x5f_union_x2f_statement_x2e_lit
