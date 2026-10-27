import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_intersection_x5f_one_x5f_bound_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_3 : Litex.IsFiniteSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_4 : Litex.IsSet _value_i2), (by
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
                    exact (Litex.finiteSetIntersectFromLeft _atomic_wd_1_0 h_3))
                )
            )
          exact h_1
        )
      )
  )

theorem h_21 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_22 : Litex.IsSet _value_i3) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_23 : Litex.IsFiniteSet _value_i4), (by
  let _object_w2 := (Litex.intersect _value_i3 _value_i4)
  exact (by
    let _atomic_wd_1_0 := _object_w2
    exact Litex.IsFiniteSet _atomic_wd_1_0)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_22 _Host_i4 _rep_i4 _value_i4 h_23
          let _object_w2 := (Litex.intersect _value_i3 _value_i4)
          have h_20 : (by
            let _atomic_wd_1_0 := _object_w2
            exact Litex.IsFiniteSet _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w2
                    exact (Litex.finiteSetIntersectFromRight _atomic_wd_1_0 h_23))
                )
            )
          exact h_20
        )
      )
  )

theorem h_43 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_56 : Litex.IsSet _value_i5) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_57 : Litex.In _value_i6 (Litex.R (M := M))), (by
  let _object_w4 := (let _wd_1_0 := (let _wd_2_0 := _value_i5;
  let _wd_2_1 := (let _setElement_0 := _value_i6;
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  (Litex.intersect _wd_2_0 _wd_2_1));
  (Litex.finiteSetSize _wd_1_0 (by
    let _atomic_wd_1_0 := (let _wd_2_0 := _value_i5;
    let _wd_2_1 := (let _setElement_0 := _value_i6;
      let _setTail_1 := Litex.emptySet (M := M);
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0);
    (Litex.intersect _wd_2_0 _wd_2_1))
    exact (Litex.finiteSetIntersectFromRight _atomic_wd_1_0 (by
      let _atomic_wd_2_0 := (let _setElement_0 := _value_i6;
        let _setTail_1 := Litex.emptySet (M := M);
        let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
        let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
        _setTail_0)
      exact (let _finite_tail_0 := _atomic_wd_2_0;
      let _finite_tail_1 := _finite_tail_0.val.tail;
      have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
      have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
      _finite_0))))))
  exact (by
    let _atomic_wd_1_0 := _object_w4
    exact Litex.In _atomic_wd_1_0 (Litex.N (M := M)))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_56 _Host_i6 _rep_i6 _value_i6 h_57
          let _object_w4 := (let _wd_1_0 := (let _wd_2_0 := _value_i5;
          let _wd_2_1 := (let _setElement_0 := _value_i6;
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (Litex.intersect _wd_2_0 _wd_2_1));
          (Litex.finiteSetSize _wd_1_0 (by
            let _atomic_wd_1_0 := (let _wd_2_0 := _value_i5;
            let _wd_2_1 := (let _setElement_0 := _value_i6;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0);
            (Litex.intersect _wd_2_0 _wd_2_1))
            exact (Litex.finiteSetIntersectFromRight _atomic_wd_1_0 (by
              let _atomic_wd_2_0 := (let _setElement_0 := _value_i6;
                let _setTail_1 := Litex.emptySet (M := M);
                let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                _setTail_0)
              exact (let _finite_tail_0 := _atomic_wd_2_0;
              let _finite_tail_1 := _finite_tail_0.val.tail;
              have _finite_1 : Litex.IsFiniteSet _finite_tail_1 := Litex.finiteSetEmpty;
              have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
              _finite_0))))))
          have h_42 : (by
            let _atomic_wd_1_0 := _object_w4
            exact Litex.In _atomic_wd_1_0 (Litex.N (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w4
                    exact (Litex.finiteSetSizeInN _atomic_wd_1_0))
                )
            )
          have h_68 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _object_w4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.naturalNonnegative _object_w4 h_42)
                )
            )
          exact h_42
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_intersection_x5f_one_x5f_bound_x2f_statement_x2e_lit
