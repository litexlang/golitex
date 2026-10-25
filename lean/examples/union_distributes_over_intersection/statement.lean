import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_union_x5f_distributes_x5f_over_x5f_intersection_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_5 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_6 : Litex.IsSet _value_i3), (by
  let _object_w1 := (let _wd_1_0 := _value_i1;
  let _wd_1_1 := (Litex.intersect _value_i2 _value_i3);
  (Litex.union _wd_1_0 _wd_1_1))
  let _object_w2 := (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
  let _wd_1_1 := (Litex.union _value_i1 _value_i3);
  (Litex.intersect _wd_1_0 _wd_1_1))
  let _object_w3 := (let _wd_1_0 := (Litex.intersect _value_i2 _value_i3);
  let _wd_1_1 := _value_i1;
  (Litex.union _wd_1_0 _wd_1_1))
  let _object_w4 := (let _wd_1_0 := (Litex.union _value_i3 _value_i1);
  let _wd_1_1 := (Litex.union _value_i1 _value_i2);
  (Litex.intersect _wd_1_0 _wd_1_1))
  exact (((by
    let _equal_wd_1_0 := _object_w1
    let _equal_wd_1_1 := _object_w2
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w3
    let _equal_wd_1_1 := _object_w4
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_4 _Host_i2 _rep_i2 _value_i2 h_5 _Host_i3 _rep_i3 _value_i3 h_6
          let _object_w1 := (let _wd_1_0 := _value_i1;
          let _wd_1_1 := (Litex.intersect _value_i2 _value_i3);
          (Litex.union _wd_1_0 _wd_1_1))
          let _object_w2 := (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
          let _wd_1_1 := (Litex.union _value_i1 _value_i3);
          (Litex.intersect _wd_1_0 _wd_1_1))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w1
            let _equal_wd_1_1 := _object_w2
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w1;
                  let _equal_wd_1_1 := _object_w2;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (let _source := _equal_wd_1_0;
                  let _target := _equal_wd_1_1;
                  let _a := _source.val.left;
                  let _b := _source.val.right.val.left;
                  let _d := _source.val.right.val.right;
                  let _ab := _target.val.left;
                  let _ad := _target.val.right;
                  ((Litex.sameRefl _source).trans ((Litex.unionIntersectDistrib _a _b _d).trans ((Litex.intersectCongr (Litex.union _a _b) (Litex.union _a _d) _ab _ad (Litex.sameRefl _ab) (Litex.sameRefl _ad)).trans (Litex.sameRefl _target)))))))
                )
            )
          let _object_w3 := (let _wd_1_0 := (Litex.intersect _value_i2 _value_i3);
          let _wd_1_1 := _value_i1;
          (Litex.union _wd_1_0 _wd_1_1))
          let _object_w4 := (let _wd_1_0 := (Litex.union _value_i3 _value_i1);
          let _wd_1_1 := (Litex.union _value_i1 _value_i2);
          (Litex.intersect _wd_1_0 _wd_1_1))
          have h_2 : (by
            let _equal_wd_1_0 := _object_w3
            let _equal_wd_1_1 := _object_w4
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w3;
                  let _equal_wd_1_1 := _object_w4;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (let _source := _equal_wd_1_0;
                  let _target := _equal_wd_1_1;
                  let _a := _source.val.right;
                  let _b := _source.val.left.val.left;
                  let _d := _source.val.left.val.right;
                  let _ab := _target.val.right;
                  let _ad := _target.val.left;
                  ((Litex.unionComm _source.val.left _source.val.right).trans ((Litex.unionIntersectDistrib _a _b _d).trans ((Litex.intersectCongr (Litex.union _a _b) (Litex.union _a _d) _ab _ad (Litex.sameRefl _ab) ((Litex.unionComm _ad.val.left _ad.val.right).symm)).trans (Litex.intersectComm _ab _ad)))))))
                )
            )
          exact (And.intro h_1 h_2)
        )
      )
  )

theorem h_16 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_17 : Litex.IsSet _value_i4) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_18 : Litex.IsSet _value_i5) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_19 : Litex.IsSet _value_i6), (by
  let _object_w5 := (let _wd_1_0 := (Litex.union _value_i5 _value_i4);
  let _wd_1_1 := (Litex.union _value_i6 _value_i4);
  (Litex.intersect _wd_1_0 _wd_1_1))
  let _object_w6 := (let _wd_1_0 := (Litex.intersect _value_i5 _value_i6);
  let _wd_1_1 := _value_i4;
  (Litex.union _wd_1_0 _wd_1_1))
  exact (by
    let _equal_wd_1_0 := _object_w5
    let _equal_wd_1_1 := _object_w6
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_17 _Host_i5 _rep_i5 _value_i5 h_18 _Host_i6 _rep_i6 _value_i6 h_19
          let _object_w5 := (let _wd_1_0 := (Litex.union _value_i5 _value_i4);
          let _wd_1_1 := (Litex.union _value_i6 _value_i4);
          (Litex.intersect _wd_1_0 _wd_1_1))
          let _object_w6 := (let _wd_1_0 := (Litex.intersect _value_i5 _value_i6);
          let _wd_1_1 := _value_i4;
          (Litex.union _wd_1_0 _wd_1_1))
          have h_15 : (by
            let _equal_wd_1_0 := _object_w5
            let _equal_wd_1_1 := _object_w6
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w5;
                  let _equal_wd_1_1 := _object_w6;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (let _source := _equal_wd_1_1;
                  let _target := _equal_wd_1_0;
                  let _a := _source.val.right;
                  let _b := _source.val.left.val.left;
                  let _d := _source.val.left.val.right;
                  let _ab := _target.val.left;
                  let _ad := _target.val.right;
                  ((Litex.unionComm _source.val.left _source.val.right).trans ((Litex.unionIntersectDistrib _a _b _d).trans ((Litex.intersectCongr (Litex.union _a _b) (Litex.union _a _d) _ab _ad ((Litex.unionComm _ab.val.left _ab.val.right).symm) ((Litex.unionComm _ad.val.left _ad.val.right).symm)).trans (Litex.sameRefl _target)))).symm)))
                )
            )
          exact h_15
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_union_x5f_distributes_x5f_over_x5f_intersection_x2f_statement_x2e_lit
