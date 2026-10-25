import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_outside_x5f_union_x5f_intersection_x2f_statement_x2e_lit

universe u v1 v2 v3 v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_7 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_8 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_9 : Litex.IsSet _value_i3) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_10 : Litex.In _value_i4 (Litex.R (M := M))) (h_1 : ¬ Litex.In _value_i4 _value_i1) (h_2 : ¬ Litex.In _value_i4 _value_i2), (by
  let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
  let _wd_1_1 := _value_i3;
  (Litex.intersect _wd_1_0 _wd_1_1))
  exact ¬ Litex.In _value_i4 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_7 _Host_i2 _rep_i2 _value_i2 h_8 _Host_i3 _rep_i3 _value_i3 h_9 _Host_i4 _rep_i4 _value_i4 h_10 h_1 h_2
          have h_17 : Litex.IsSet _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  h_7
                )
            )
          have h_18 : Litex.IsSet _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  h_8
                )
            )
          have h_19 : Litex.IsSet _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  h_9
                )
            )
          have h_20 : Litex.In _value_i4 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_10
                )
            )
          let _object_w3 := (Litex.union _value_i1 _value_i2)

          have h_5 : (by
            let _atomic_wd_1_1 := _object_w3
            exact ¬ Litex.In _value_i4 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w3
                    exact (let _set := _atomic_wd_1_1; Litex.notInUnion _value_i4 _set.val.left _set.val.right h_1 h_2))
                )
            )
          let _object_w4 := (let _wd_1_0 := _object_w3;
          let _wd_1_1 := _value_i3;
          (Litex.intersect _wd_1_0 _wd_1_1))

          have h_6 : (by
            let _atomic_wd_1_1 := _object_w4
            exact ¬ Litex.In _value_i4 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w4
                    exact (let _set := _atomic_wd_1_1; Litex.notInIntersectOfLeft _value_i4 _set.val.left _set.val.right (by
                      let _atomic_wd_2_1 := _object_w3
                      exact h_5)))
                )
            )
          exact (by
            let _atomic_wd_1_1 := _object_w4
            exact h_6)
        )
      )
  )

theorem h_122 : ¬ Litex.In (Litex.number (M := M) (1 : ℂ)) (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0);
let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0);
(Litex.union _wd_2_0 _wd_2_1));
let _wd_1_1 := (Litex.R (M := M));
(Litex.intersect _wd_1_0 _wd_1_1)) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_116 : (by
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
          have h_117 : (by
            let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact Litex.IsSet _atomic_wd_1_0) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (Litex.isSet _atomic_wd_1_0))
                )
            )
          have h_118 : Litex.IsSet (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.isSet (Litex.R (M := M)))
                )
            )
          have h_119 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
                )
            )
          have h_120 : (by
            let _atomic_wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact ¬ Litex.In (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (by
                      let _set := _atomic_wd_1_1
                      exact (Litex.notInInsert (Litex.number (M := M) (1 : ℂ)) _set.val.element _set.val.tail _set.wd (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (1 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) (Litex.notInEmpty (Litex.number (M := M) (1 : ℂ))))))
                )
            )
          have h_121 : (by
            let _atomic_wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact ¬ Litex.In (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact (by
                      let _set := _atomic_wd_1_1
                      exact (Litex.notInInsert (Litex.number (M := M) (1 : ℂ)) _set.val.element _set.val.tail _set.wd (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty (Litex.number (M := M) (1 : ℂ))))))
                )
            )
          exact ((h_4 (M := M)) (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) h_116 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0) h_117 (Litex.R (M := M)) h_118 (Litex.number (M := M) (1 : ℂ)) h_119 h_120 h_121)
        )
      )
  )

theorem h_149 : (by
  let _atomic_wd_1_1 := (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  (Litex.union _wd_2_0 _wd_2_1));
  let _wd_1_1 := (Litex.R (M := M));
  (Litex.intersect _wd_1_0 _wd_1_1))
  exact ¬ Litex.In (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_1 := (let _wd_1_0 := (let _wd_2_0 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          let _wd_2_1 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (Litex.union _wd_2_0 _wd_2_1));
          let _wd_1_1 := (Litex.R (M := M));
          (Litex.intersect _wd_1_0 _wd_1_1))
          exact (h_122 (M := M)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_outside_x5f_union_x5f_intersection_x2f_statement_x2e_lit
