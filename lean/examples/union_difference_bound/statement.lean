import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_union_x5f_difference_x5f_bound_x2f_statement_x2e_lit

universe u v1 v2 v3 v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_7 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_8 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_9 : Litex.IsSet _value_i3) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_10 : Litex.IsSet _value_i4) (h_1 : Litex.Subset _value_i1 _value_i4) (h_2 : Litex.Subset _value_i2 _value_i4), (by
  let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
  let _wd_1_1 := _value_i3;
  (Litex.setMinus _wd_1_0 _wd_1_1))
  exact Litex.Subset _atomic_wd_1_0 _value_i4) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_7 _Host_i2 _rep_i2 _value_i2 h_8 _Host_i3 _rep_i3 _value_i3 h_9 _Host_i4 _rep_i4 _value_i4 h_10 h_1 h_2
          have h_20 : Litex.IsSet _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  h_7
                )
            )
          have h_21 : Litex.IsSet _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  h_8
                )
            )
          have h_22 : Litex.IsSet _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  h_9
                )
            )
          have h_23 : Litex.IsSet _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          let _object_w1 := (Litex.union _value_i1 _value_i2)

          have h_5 : (by
            let _atomic_wd_1_0 := _object_w1
            exact Litex.Subset _atomic_wd_1_0 _value_i4) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w1
                    exact (let _union := _atomic_wd_1_0; Litex.unionSubsetOfBoth _union.val.left _union.val.right _value_i4 h_1 h_2))
                )
            )
          let _object_w2 := (let _wd_1_0 := _object_w1;
          let _wd_1_1 := _value_i3;
          (Litex.setMinus _wd_1_0 _wd_1_1))

          have h_6 : (by
            let _atomic_wd_1_0 := _object_w2
            exact Litex.Subset _atomic_wd_1_0 _value_i4) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w2
                    exact (let _set := _atomic_wd_1_0; Litex.setMinusSubsetOfLeft _set.val.left _set.val.right _value_i4 (by
                      let _atomic_wd_2_0 := _object_w1
                      exact h_5)))
                )
            )
          exact (by
            let _atomic_wd_1_0 := _object_w2
            exact h_6)
        )
      )
  )

theorem h_101 : (by
  let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.union (Litex.Q (M := M)) (Litex.Z (M := M)));
  let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  (Litex.setMinus _wd_1_0 _wd_1_1))
  exact Litex.Subset _atomic_wd_1_0 (Litex.R (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_102 : Litex.IsSet (Litex.Q (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.isSet (Litex.Q (M := M)))
                )
            )
          have h_103 : Litex.IsSet (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.isSet (Litex.Z (M := M)))
                )
            )
          have h_104 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact Litex.IsSet _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (Litex.isSet _atomic_wd_1_0))
                )
            )
          have h_105 : Litex.IsSet (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.isSet (Litex.R (M := M)))
                )
            )
          have h_106 : Litex.Subset (Litex.Q (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.subsetOfForall (Litex.Q (M := M)) (Litex.R (M := M)) (fun _a _ha => (Litex.rationalToReal _a _ha)))
                )
            )
          have h_107 : Litex.Subset (Litex.Z (M := M)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.subsetOfForall (Litex.Z (M := M)) (Litex.R (M := M)) (fun _a _ha => (Litex.integerToReal _a _ha)))
                )
            )
          have h_108 : Litex.Subset (let _wd_1_0 := (Litex.union (Litex.Q (M := M)) (Litex.Z (M := M)));
          let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (Litex.setMinus _wd_1_0 _wd_1_1)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_4 (M := M)) (Litex.Q (M := M)) h_102 (Litex.Z (M := M)) h_103 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0) h_104 (Litex.R (M := M)) h_105 h_106 h_107)
                )
            )
          exact (by
          let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.union (Litex.Q (M := M)) (Litex.Z (M := M)));
          let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (Litex.setMinus _wd_1_0 _wd_1_1))
          exact h_108)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_union_x5f_difference_x5f_bound_x2f_statement_x2e_lit
