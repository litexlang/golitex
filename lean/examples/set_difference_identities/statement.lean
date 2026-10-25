import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_set_x5f_difference_x5f_identities_x2f_statement_x2e_lit

universe u v1 v2 v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_8 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_9 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_10 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_11 : Litex.IsSet _value_i3), (by
  let _object_w1 := (Litex.setMinus _value_i1 _value_i1)
  let _object_w2 := (let _setTail_0 := Litex.emptySet (M := M);
    _setTail_0)
  let _object_w3 := (let _wd_1_0 := _value_i1;
  let _wd_1_1 := _object_w2;
  (Litex.setMinus _wd_1_0 _wd_1_1))
  let _object_w4 := (let _wd_1_0 := _object_w2;
  let _wd_1_1 := _value_i1;
  (Litex.setMinus _wd_1_0 _wd_1_1))
  let _object_w5 := (let _wd_1_0 := _value_i1;
  let _wd_1_1 := (Litex.union _value_i2 _value_i3);
  (Litex.setMinus _wd_1_0 _wd_1_1))
  let _object_w6 := (let _wd_1_0 := (Litex.setMinus _value_i1 _value_i2);
  let _wd_1_1 := (Litex.setMinus _value_i1 _value_i3);
  (Litex.intersect _wd_1_0 _wd_1_1))
  let _object_w7 := (let _wd_1_0 := _value_i1;
  let _wd_1_1 := (Litex.intersect _value_i2 _value_i3);
  (Litex.setMinus _wd_1_0 _wd_1_1))
  let _object_w8 := (let _wd_1_0 := (Litex.setMinus _value_i1 _value_i2);
  let _wd_1_1 := (Litex.setMinus _value_i1 _value_i3);
  (Litex.union _wd_1_0 _wd_1_1))
  let _object_w9 := (let _wd_1_0 := _value_i1;
  let _wd_1_1 := (Litex.setMinus _value_i2 _wd_1_0);
  (Litex.intersect _wd_1_0 _wd_1_1))
  let _object_w10 := (let _wd_1_0 := (Litex.setMinus _value_i2 _value_i1);
  let _wd_1_1 := _value_i1;
  (Litex.intersect _wd_1_0 _wd_1_1))
  exact (((by
    let _equal_wd_1_0 := _object_w1
    let _equal_wd_1_1 := _object_w2
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w3
    exact Litex.Same _equal_wd_1_0 _value_i1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w4
    let _equal_wd_1_1 := _object_w2
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w5
    let _equal_wd_1_1 := _object_w6
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w7
    let _equal_wd_1_1 := _object_w8
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w9
    let _equal_wd_1_1 := _object_w2
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w10
    let _equal_wd_1_1 := _object_w2
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))))))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_9 _Host_i2 _rep_i2 _value_i2 h_10 _Host_i3 _rep_i3 _value_i3 h_11
          let _object_w1 := (Litex.setMinus _value_i1 _value_i1)
          let _object_w2 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0)
          have h_1 : (by
            let _equal_wd_1_0 := _object_w1
            let _equal_wd_1_1 := _object_w2
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w1;
                  let _equal_wd_1_1 := _object_w2;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (let _set := _equal_wd_1_0; (Litex.setMinusSelf _set.val.left))))
                )
            )
          let _object_w3 := (let _wd_1_0 := _value_i1;
          let _wd_1_1 := _object_w2;
          (Litex.setMinus _wd_1_0 _wd_1_1))
          have h_2 : (by
            let _equal_wd_1_0 := _object_w3
            exact Litex.Same _equal_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w3;
                  (show Litex.Same _equal_wd_1_0 _value_i1 from (let _set := _equal_wd_1_0; (Litex.setMinusEmptyRight _set.val.left))))
                )
            )
          let _object_w4 := (let _wd_1_0 := _object_w2;
          let _wd_1_1 := _value_i1;
          (Litex.setMinus _wd_1_0 _wd_1_1))
          have h_3 : (by
            let _equal_wd_1_0 := _object_w4
            let _equal_wd_1_1 := _object_w2
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w4;
                  let _equal_wd_1_1 := _object_w2;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (let _set := _equal_wd_1_0; (Litex.setMinusEmptyLeft _set.val.right))))
                )
            )
          let _object_w5 := (let _wd_1_0 := _value_i1;
          let _wd_1_1 := (Litex.union _value_i2 _value_i3);
          (Litex.setMinus _wd_1_0 _wd_1_1))
          let _object_w6 := (let _wd_1_0 := (Litex.setMinus _value_i1 _value_i2);
          let _wd_1_1 := (Litex.setMinus _value_i1 _value_i3);
          (Litex.intersect _wd_1_0 _wd_1_1))
          have h_4 : (by
            let _equal_wd_1_0 := _object_w5
            let _equal_wd_1_1 := _object_w6
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w5;
                  let _equal_wd_1_1 := _object_w6;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (let _set := _equal_wd_1_0; (Litex.setMinusUnion _set.val.left _set.val.right.val.left _set.val.right.val.right))))
                )
            )
          let _object_w7 := (let _wd_1_0 := _value_i1;
          let _wd_1_1 := (Litex.intersect _value_i2 _value_i3);
          (Litex.setMinus _wd_1_0 _wd_1_1))
          let _object_w8 := (let _wd_1_0 := (Litex.setMinus _value_i1 _value_i2);
          let _wd_1_1 := (Litex.setMinus _value_i1 _value_i3);
          (Litex.union _wd_1_0 _wd_1_1))
          have h_5 : (by
            let _equal_wd_1_0 := _object_w7
            let _equal_wd_1_1 := _object_w8
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w7;
                  let _equal_wd_1_1 := _object_w8;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (let _set := _equal_wd_1_0; (Litex.setMinusIntersect _set.val.left _set.val.right.val.left _set.val.right.val.right))))
                )
            )
          let _object_w9 := (let _wd_1_0 := _value_i1;
          let _wd_1_1 := (Litex.setMinus _value_i2 _wd_1_0);
          (Litex.intersect _wd_1_0 _wd_1_1))
          have h_6 : (by
            let _equal_wd_1_0 := _object_w9
            let _equal_wd_1_1 := _object_w2
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w9;
                  let _equal_wd_1_1 := _object_w2;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (let _set := _equal_wd_1_0; (Litex.intersectSetMinusEmpty _set.val.left _set.val.right.val.left))))
                )
            )
          let _object_w10 := (let _wd_1_0 := (Litex.setMinus _value_i2 _value_i1);
          let _wd_1_1 := _value_i1;
          (Litex.intersect _wd_1_0 _wd_1_1))
          have h_7 : (by
            let _equal_wd_1_0 := _object_w10
            let _equal_wd_1_1 := _object_w2
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w10;
                  let _equal_wd_1_1 := _object_w2;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (let _set := _equal_wd_1_0; (Litex.setMinusIntersectEmpty _set.val.right _set.val.left.val.left))))
                )
            )
          exact (And.intro h_1 (And.intro h_2 (And.intro h_3 (And.intro h_4 (And.intro h_5 (And.intro h_6 h_7))))))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_set_x5f_difference_x5f_identities_x2f_statement_x2e_lit
