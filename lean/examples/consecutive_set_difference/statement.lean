import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_consecutive_x5f_set_x5f_difference_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_5 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_6 : Litex.IsSet _value_i3), (by
  let _object_w1 := (let _wd_1_0 := (Litex.setMinus _value_i1 _value_i2);
  let _wd_1_1 := _value_i3;
  (Litex.setMinus _wd_1_0 _wd_1_1))
  let _object_w2 := (let _wd_1_0 := _value_i1;
  let _wd_1_1 := (Litex.union _value_i2 _value_i3);
  (Litex.setMinus _wd_1_0 _wd_1_1))
  let _object_w3 := (let _wd_1_0 := _value_i1;
  let _wd_1_1 := (Litex.union _value_i3 _value_i2);
  (Litex.setMinus _wd_1_0 _wd_1_1))
  exact (((by
    let _equal_wd_1_0 := _object_w1
    let _equal_wd_1_1 := _object_w2
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w1
    let _equal_wd_1_1 := _object_w3
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_4 _Host_i2 _rep_i2 _value_i2 h_5 _Host_i3 _rep_i3 _value_i3 h_6
          let _object_w1 := (let _wd_1_0 := (Litex.setMinus _value_i1 _value_i2);
          let _wd_1_1 := _value_i3;
          (Litex.setMinus _wd_1_0 _wd_1_1))
          let _object_w2 := (let _wd_1_0 := _value_i1;
          let _wd_1_1 := (Litex.union _value_i2 _value_i3);
          (Litex.setMinus _wd_1_0 _wd_1_1))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w1
            let _equal_wd_1_1 := _object_w2
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w1;
                  let _equal_wd_1_1 := _object_w2;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (let _set := _equal_wd_1_0; (Litex.setMinusChain _set.val.left.val.left _set.val.left.val.right _set.val.right))))
                )
            )
          let _object_w3 := (let _wd_1_0 := _value_i1;
          let _wd_1_1 := (Litex.union _value_i3 _value_i2);
          (Litex.setMinus _wd_1_0 _wd_1_1))
          have h_2 : (by
            let _equal_wd_1_0 := _object_w1
            let _equal_wd_1_1 := _object_w3
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w1;
                  let _equal_wd_1_1 := _object_w3;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (let _set := _equal_wd_1_0; (Litex.setMinusChainSwap _set.val.left.val.left _set.val.left.val.right _set.val.right))))
                )
            )
          exact (And.intro h_1 h_2)
        )
      )
  )

theorem h_21 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_23 : Litex.IsSet _value_i4) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_24 : Litex.IsSet _value_i5) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_25 : Litex.IsSet _value_i6), (by
  let _object_w4 := (let _wd_1_0 := _value_i4;
  let _wd_1_1 := (Litex.union _value_i5 _value_i6);
  (Litex.setMinus _wd_1_0 _wd_1_1))
  let _object_w5 := (let _wd_1_0 := (Litex.setMinus _value_i4 _value_i5);
  let _wd_1_1 := _value_i6;
  (Litex.setMinus _wd_1_0 _wd_1_1))
  let _object_w6 := (let _wd_1_0 := _value_i4;
  let _wd_1_1 := (Litex.union _value_i6 _value_i5);
  (Litex.setMinus _wd_1_0 _wd_1_1))
  exact (((by
    let _equal_wd_1_0 := _object_w4
    let _equal_wd_1_1 := _object_w5
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w6
    let _equal_wd_1_1 := _object_w5
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_23 _Host_i5 _rep_i5 _value_i5 h_24 _Host_i6 _rep_i6 _value_i6 h_25
          let _object_w4 := (let _wd_1_0 := _value_i4;
          let _wd_1_1 := (Litex.union _value_i5 _value_i6);
          (Litex.setMinus _wd_1_0 _wd_1_1))
          let _object_w5 := (let _wd_1_0 := (Litex.setMinus _value_i4 _value_i5);
          let _wd_1_1 := _value_i6;
          (Litex.setMinus _wd_1_0 _wd_1_1))
          have h_19 : (by
            let _equal_wd_1_0 := _object_w4
            let _equal_wd_1_1 := _object_w5
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w4;
                  let _equal_wd_1_1 := _object_w5;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (let _set := _equal_wd_1_1; (Litex.setMinusChain _set.val.left.val.left _set.val.left.val.right _set.val.right).symm)))
                )
            )
          let _object_w6 := (let _wd_1_0 := _value_i4;
          let _wd_1_1 := (Litex.union _value_i6 _value_i5);
          (Litex.setMinus _wd_1_0 _wd_1_1))
          have h_20 : (by
            let _equal_wd_1_0 := _object_w6
            let _equal_wd_1_1 := _object_w5
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w6;
                  let _equal_wd_1_1 := _object_w5;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (let _set := _equal_wd_1_1; (Litex.setMinusChainSwap _set.val.left.val.left _set.val.left.val.right _set.val.right).symm)))
                )
            )
          exact (And.intro h_19 h_20)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_consecutive_x5f_set_x5f_difference_x2f_statement_x2e_lit
