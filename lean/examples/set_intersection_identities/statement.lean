import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_set_x5f_intersection_x5f_identities_x2f_statement_x2e_lit

universe u v1 v2 v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_6 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_7 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_8 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_9 : Litex.IsSet _value_i3), (by
  let _object_w1 := (Litex.intersect _value_i1 _value_i2)
  let _object_w2 := (Litex.intersect _value_i2 _value_i1)
  let _object_w3 := (Litex.intersect _value_i1 _value_i1)
  let _object_w4 := (let _wd_1_0 := _value_i1;
  let _wd_1_1 := (let _setTail_0 := Litex.emptySet (M := M);
    _setTail_0);
  (Litex.intersect _wd_1_0 _wd_1_1))
  let _object_w5 := (let _setTail_0 := Litex.emptySet (M := M);
    _setTail_0)
  let _object_w6 := (let _wd_1_0 := _object_w5;
  let _wd_1_1 := _value_i1;
  (Litex.intersect _wd_1_0 _wd_1_1))
  let _object_w7 := (let _wd_1_0 := _object_w1;
  let _wd_1_1 := _value_i3;
  (Litex.intersect _wd_1_0 _wd_1_1))
  let _object_w8 := (let _wd_1_0 := _value_i1;
  let _wd_1_1 := (Litex.intersect _value_i2 _value_i3);
  (Litex.intersect _wd_1_0 _wd_1_1))
  exact (((by
    let _equal_wd_1_0 := _object_w1
    let _equal_wd_1_1 := _object_w2
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w3
    exact Litex.Same _equal_wd_1_0 _value_i1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w4
    let _equal_wd_1_1 := _object_w5
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w6
    let _equal_wd_1_1 := _object_w5
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w7
    let _equal_wd_1_1 := _object_w8
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_7 _Host_i2 _rep_i2 _value_i2 h_8 _Host_i3 _rep_i3 _value_i3 h_9
          let _object_w1 := (Litex.intersect _value_i1 _value_i2)
          let _object_w2 := (Litex.intersect _value_i2 _value_i1)
          have h_1 : (by
            let _equal_wd_1_0 := _object_w1
            let _equal_wd_1_1 := _object_w2
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w1;
                  let _equal_wd_1_1 := _object_w2;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (let _litex_set := _equal_wd_1_0; (Litex.intersectComm _litex_set.val.left _litex_set.val.right))))
                )
            )
          let _object_w3 := (Litex.intersect _value_i1 _value_i1)
          have h_2 : (by
            let _equal_wd_1_0 := _object_w3
            exact Litex.Same _equal_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w3;
                  (show Litex.Same _equal_wd_1_0 _value_i1 from (let _litex_set := _equal_wd_1_0; (Litex.intersectIdem _litex_set.val.left))))
                )
            )
          let _object_w4 := (let _wd_1_0 := _value_i1;
          let _wd_1_1 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0);
          (Litex.intersect _wd_1_0 _wd_1_1))
          let _object_w5 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0)
          have h_3 : (by
            let _equal_wd_1_0 := _object_w4
            let _equal_wd_1_1 := _object_w5
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w4;
                  let _equal_wd_1_1 := _object_w5;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (let _litex_set := _equal_wd_1_0; (Litex.intersectEmptyRight _litex_set.val.left))))
                )
            )
          let _object_w6 := (let _wd_1_0 := _object_w5;
          let _wd_1_1 := _value_i1;
          (Litex.intersect _wd_1_0 _wd_1_1))
          have h_4 : (by
            let _equal_wd_1_0 := _object_w6
            let _equal_wd_1_1 := _object_w5
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w6;
                  let _equal_wd_1_1 := _object_w5;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (let _litex_set := _equal_wd_1_0; (Litex.intersectEmptyLeft _litex_set.val.right))))
                )
            )
          let _object_w7 := (let _wd_1_0 := _object_w1;
          let _wd_1_1 := _value_i3;
          (Litex.intersect _wd_1_0 _wd_1_1))
          let _object_w8 := (let _wd_1_0 := _value_i1;
          let _wd_1_1 := (Litex.intersect _value_i2 _value_i3);
          (Litex.intersect _wd_1_0 _wd_1_1))
          have h_5 : (by
            let _equal_wd_1_0 := _object_w7
            let _equal_wd_1_1 := _object_w8
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w7;
                  let _equal_wd_1_1 := _object_w8;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (let _litex_set := _equal_wd_1_0; (Litex.intersectAssoc _litex_set.val.left.val.left _litex_set.val.left.val.right _litex_set.val.right))))
                )
            )
          exact (And.intro h_1 (And.intro h_2 (And.intro h_3 (And.intro h_4 h_5))))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_set_x5f_intersection_x5f_identities_x2f_statement_x2e_lit
