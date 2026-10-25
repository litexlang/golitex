import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_set_x5f_identity_x5f_symmetry_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_10 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_11 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_12 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_13 : Litex.IsSet _value_i3), (by
  let _object_w1 := (Litex.intersect _value_i1 _value_i1)
  let _object_w2 := (let _setTail_0 := Litex.emptySet (M := M);
    _setTail_0)
  let _object_w3 := (let _wd_1_0 := _value_i1;
  let _wd_1_1 := (let _setTail_0 := Litex.emptySet (M := M);
    _setTail_0);
  (Litex.intersect _wd_1_0 _wd_1_1))
  let _object_w4 := (let _wd_1_0 := _object_w2;
  let _wd_1_1 := _value_i1;
  (Litex.intersect _wd_1_0 _wd_1_1))
  let _object_w5 := (let _wd_1_0 := _value_i1;
  let _wd_1_1 := (Litex.intersect _value_i2 _value_i3);
  (Litex.intersect _wd_1_0 _wd_1_1))
  let _object_w6 := (let _wd_1_0 := (Litex.intersect _value_i1 _value_i2);
  let _wd_1_1 := _value_i3;
  (Litex.intersect _wd_1_0 _wd_1_1))
  let _object_w7 := (Litex.union _value_i1 _value_i1)
  let _object_w8 := (let _wd_1_0 := _value_i1;
  let _wd_1_1 := _object_w2;
  (Litex.union _wd_1_0 _wd_1_1))
  let _object_w9 := (let _wd_1_0 := _object_w2;
  let _wd_1_1 := _value_i1;
  (Litex.union _wd_1_0 _wd_1_1))
  let _object_w10 := (let _wd_1_0 := _value_i1;
  let _wd_1_1 := (Litex.union _value_i2 _value_i3);
  (Litex.union _wd_1_0 _wd_1_1))
  let _object_w11 := (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
  let _wd_1_1 := _value_i3;
  (Litex.union _wd_1_0 _wd_1_1))
  let _object_w12 := (let _wd_1_0 := (Litex.intersect _value_i1 _value_i2);
  let _wd_1_1 := (Litex.intersect _value_i1 _value_i3);
  (Litex.union _wd_1_0 _wd_1_1))
  let _object_w13 := (let _wd_1_0 := _value_i1;
  let _wd_1_1 := (Litex.union _value_i2 _value_i3);
  (Litex.intersect _wd_1_0 _wd_1_1))
  exact (((by
    let _equal_wd_1_1 := _object_w1
    exact Litex.Same _value_i1 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w2
    let _equal_wd_1_1 := _object_w3
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w2
    let _equal_wd_1_1 := _object_w4
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w5
    let _equal_wd_1_1 := _object_w6
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_1 := _object_w7
    exact Litex.Same _value_i1 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_1 := _object_w8
    exact Litex.Same _value_i1 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_1 := _object_w9
    exact Litex.Same _value_i1 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w10
    let _equal_wd_1_1 := _object_w11
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w12
    let _equal_wd_1_1 := _object_w13
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))))))))))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_11 _Host_i2 _rep_i2 _value_i2 h_12 _Host_i3 _rep_i3 _value_i3 h_13
          let _object_w1 := (Litex.intersect _value_i1 _value_i1)
          have h_1 : (by
            let _equal_wd_1_1 := _object_w1
            exact Litex.Same _value_i1 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_1 := _object_w1;
                  (show Litex.Same _value_i1 _equal_wd_1_1 from (let _litex_set := _equal_wd_1_1; (Litex.intersectIdem _litex_set.val.left).symm)))
                )
            )
          let _object_w2 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0)
          let _object_w3 := (let _wd_1_0 := _value_i1;
          let _wd_1_1 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0);
          (Litex.intersect _wd_1_0 _wd_1_1))
          have h_2 : (by
            let _equal_wd_1_0 := _object_w2
            let _equal_wd_1_1 := _object_w3
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w2;
                  let _equal_wd_1_1 := _object_w3;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (let _litex_set := _equal_wd_1_1; (Litex.intersectEmptyRight _litex_set.val.left).symm)))
                )
            )
          let _object_w4 := (let _wd_1_0 := _object_w2;
          let _wd_1_1 := _value_i1;
          (Litex.intersect _wd_1_0 _wd_1_1))
          have h_3 : (by
            let _equal_wd_1_0 := _object_w2
            let _equal_wd_1_1 := _object_w4
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w2;
                  let _equal_wd_1_1 := _object_w4;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (let _litex_set := _equal_wd_1_1; (Litex.intersectEmptyLeft _litex_set.val.right).symm)))
                )
            )
          let _object_w5 := (let _wd_1_0 := _value_i1;
          let _wd_1_1 := (Litex.intersect _value_i2 _value_i3);
          (Litex.intersect _wd_1_0 _wd_1_1))
          let _object_w6 := (let _wd_1_0 := (Litex.intersect _value_i1 _value_i2);
          let _wd_1_1 := _value_i3;
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
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (let _litex_set := _equal_wd_1_1; (Litex.intersectAssoc _litex_set.val.left.val.left _litex_set.val.left.val.right _litex_set.val.right).symm)))
                )
            )
          let _object_w7 := (Litex.union _value_i1 _value_i1)
          have h_5 : (by
            let _equal_wd_1_1 := _object_w7
            exact Litex.Same _value_i1 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_1 := _object_w7;
                  (show Litex.Same _value_i1 _equal_wd_1_1 from (let _litex_set := _equal_wd_1_1; (Litex.unionIdem _litex_set.val.left).symm)))
                )
            )
          let _object_w8 := (let _wd_1_0 := _value_i1;
          let _wd_1_1 := _object_w2;
          (Litex.union _wd_1_0 _wd_1_1))
          have h_6 : (by
            let _equal_wd_1_1 := _object_w8
            exact Litex.Same _value_i1 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_1 := _object_w8;
                  (show Litex.Same _value_i1 _equal_wd_1_1 from (let _litex_set := _equal_wd_1_1; (Litex.unionEmptyRight _litex_set.val.left).symm)))
                )
            )
          let _object_w9 := (let _wd_1_0 := _object_w2;
          let _wd_1_1 := _value_i1;
          (Litex.union _wd_1_0 _wd_1_1))
          have h_7 : (by
            let _equal_wd_1_1 := _object_w9
            exact Litex.Same _value_i1 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_1 := _object_w9;
                  (show Litex.Same _value_i1 _equal_wd_1_1 from (let _litex_set := _equal_wd_1_1; (Litex.unionEmptyLeft _litex_set.val.right).symm)))
                )
            )
          let _object_w10 := (let _wd_1_0 := _value_i1;
          let _wd_1_1 := (Litex.union _value_i2 _value_i3);
          (Litex.union _wd_1_0 _wd_1_1))
          let _object_w11 := (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
          let _wd_1_1 := _value_i3;
          (Litex.union _wd_1_0 _wd_1_1))
          have h_8 : (by
            let _equal_wd_1_0 := _object_w10
            let _equal_wd_1_1 := _object_w11
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w10;
                  let _equal_wd_1_1 := _object_w11;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (let _litex_set := _equal_wd_1_1; (Litex.unionAssoc _litex_set.val.left.val.left _litex_set.val.left.val.right _litex_set.val.right).symm)))
                )
            )
          let _object_w12 := (let _wd_1_0 := (Litex.intersect _value_i1 _value_i2);
          let _wd_1_1 := (Litex.intersect _value_i1 _value_i3);
          (Litex.union _wd_1_0 _wd_1_1))
          let _object_w13 := (let _wd_1_0 := _value_i1;
          let _wd_1_1 := (Litex.union _value_i2 _value_i3);
          (Litex.intersect _wd_1_0 _wd_1_1))
          have h_9 : (by
            let _equal_wd_1_0 := _object_w12
            let _equal_wd_1_1 := _object_w13
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w12;
                  let _equal_wd_1_1 := _object_w13;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (let _litex_set := _equal_wd_1_1; (Litex.intersectUnionDistrib _litex_set.val.left _litex_set.val.right.val.left _litex_set.val.right.val.right).symm)))
                )
            )
          exact (And.intro h_1 (And.intro h_2 (And.intro h_3 (And.intro h_4 (And.intro h_5 (And.intro h_6 (And.intro h_7 (And.intro h_8 h_9))))))))
        )
      )
  )

theorem h_57 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_58 : Litex.IsSet _value_i4) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_59 : Litex.IsSet _value_i5) (h_54 : Litex.Subset _value_i4 _value_i5), (by
  let _object_w14 := (Litex.intersect _value_i4 _value_i5)
  let _object_w15 := (Litex.intersect _value_i5 _value_i4)
  exact (((by
    let _equal_wd_1_1 := _object_w14
    exact Litex.Same _value_i4 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_1 := _object_w15
    exact Litex.Same _value_i4 _equal_wd_1_1)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_58 _Host_i5 _rep_i5 _value_i5 h_59 h_54
          let _object_w14 := (Litex.intersect _value_i4 _value_i5)
          have h_55 : (by
            let _equal_wd_1_1 := _object_w14
            exact Litex.Same _value_i4 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_1 := _object_w14;
                  (show Litex.Same _value_i4 _equal_wd_1_1 from (let _litex_set := _equal_wd_1_1; (Litex.intersectOfSubsetLeft _litex_set.val.left _litex_set.val.right h_54).symm)))
                )
            )
          let _object_w15 := (Litex.intersect _value_i5 _value_i4)
          have h_56 : (by
            let _equal_wd_1_1 := _object_w15
            exact Litex.Same _value_i4 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_1 := _object_w15;
                  (show Litex.Same _value_i4 _equal_wd_1_1 from (let _litex_set := _equal_wd_1_1; (Litex.intersectOfSubsetRight _litex_set.val.left _litex_set.val.right h_54).symm)))
                )
            )
          exact (And.intro h_55 h_56)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_set_x5f_identity_x5f_symmetry_x2f_statement_x2e_lit
