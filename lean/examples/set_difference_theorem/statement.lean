import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_set_x5f_difference_x5f_theorem_x2f_statement_x2e_lit

universe u v1 v2 v3 v5 v6 v7 v8
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_5 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_6 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_7 : Litex.In _value_i3 _value_i1) (h_1 : ¬ Litex.In _value_i3 _value_i2), (by
  let _atomic_wd_1_1 := (Litex.setMinus _value_i1 _value_i2)
  exact Litex.In _value_i3 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_5 _Host_i2 _rep_i2 _value_i2 h_6 _Host_i3 _rep_i3 _value_i3 h_7 h_1
          have h_10 : Litex.IsSet _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  h_5
                )
            )
          have h_11 : Litex.IsSet _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          have h_12 : Litex.In _value_i3 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  h_7
                )
            )
          let _object_w1 := (Litex.setMinus _value_i1 _value_i2)

          have h_4 : (by
            let _atomic_wd_1_1 := _object_w1
            exact Litex.In _value_i3 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w1
                    exact (let _set := _atomic_wd_1_1; (Litex.inSetMinus_iff _value_i3 _set.val.left _set.val.right).mpr ⟨h_12, h_1⟩))
                )
            )

          have h_31 : Litex.In _value_i3 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (let _set := _object_w1; ((Litex.inSetMinus_iff _value_i3 _set.val.left _set.val.right).mp h_4).1)
                )
            )

          have h_32 : ¬ Litex.In _value_i3 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (let _set := _object_w1; ((Litex.inSetMinus_iff _value_i3 _set.val.left _set.val.right).mp h_4).2)
                )
            )
          exact (by
            let _atomic_wd_1_1 := _object_w1
            exact h_4)
        )
      )
  )

theorem h_46 : (by
  let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.R (M := M));
  let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  (Litex.setMinus _wd_1_0 _wd_1_1))
  exact Litex.In (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_47 : Litex.IsSet (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.isSet (Litex.R (M := M)))
                )
            )
          have h_48 : (by
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
          have h_49 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
                )
            )
          have h_50 : (by
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
          have h_51 : Litex.In (Litex.number (M := M) (1 : ℂ)) (let _wd_1_0 := (Litex.R (M := M));
          let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (Litex.setMinus _wd_1_0 _wd_1_1)) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_3 (M := M)) (Litex.R (M := M)) h_47 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0) h_48 (Litex.number (M := M) (1 : ℂ)) h_49 h_50)
                )
            )
          have h_59 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (let _set := (let _wd_1_0 := (Litex.R (M := M));
                  let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.setMinus _wd_1_0 _wd_1_1)); ((Litex.inSetMinus_iff (Litex.number (M := M) (1 : ℂ)) _set.val.left _set.val.right).mp h_51).1)
                )
            )
          have h_60 : ¬ Litex.In (Litex.number (M := M) (1 : ℂ)) (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0) :=
            (by
              litex_checked_step =>
                exact (
                  (let _set := (let _wd_1_0 := (Litex.R (M := M));
                  let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.setMinus _wd_1_0 _wd_1_1)); ((Litex.inSetMinus_iff (Litex.number (M := M) (1 : ℂ)) _set.val.left _set.val.right).mp h_51).2)
                )
            )
          have h_61 : ¬ Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (let _set := (let _wd_1_0 := (Litex.R (M := M));
                  let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.setMinus _wd_1_0 _wd_1_1)); (fun _same => ((Litex.inSetMinus_iff (Litex.number (M := M) (1 : ℂ)) _set.val.left _set.val.right).mp h_51).2 ((Litex.inInsert_iff (Litex.number (M := M) (1 : ℂ)) _set.val.right.val.element _set.val.right.val.tail _set.val.right.wd).mpr (Or.inl _same))))
                )
            )
          exact (by
          let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.R (M := M));
          let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (Litex.setMinus _wd_1_0 _wd_1_1))
          exact h_51)
        )
      )
  )

theorem h_66 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (let _set := (let _wd_1_0 := (Litex.R (M := M));
        let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0);
        (Litex.setMinus _wd_1_0 _wd_1_1)); ((Litex.inSetMinus_iff (Litex.number (M := M) (1 : ℂ)) _set.val.left _set.val.right).mp (h_46 (M := M))).1)
      )
  )

theorem h_67 : ¬ Litex.In (Litex.number (M := M) (1 : ℂ)) (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) :=
  (by
    litex_complete =>
      exact (
        (let _set := (let _wd_1_0 := (Litex.R (M := M));
        let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0);
        (Litex.setMinus _wd_1_0 _wd_1_1)); ((Litex.inSetMinus_iff (Litex.number (M := M) (1 : ℂ)) _set.val.left _set.val.right).mp (h_46 (M := M))).2)
      )
  )

theorem h_68 : ¬ Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (let _set := (let _wd_1_0 := (Litex.R (M := M));
        let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0);
        (Litex.setMinus _wd_1_0 _wd_1_1)); (fun _same => ((Litex.inSetMinus_iff (Litex.number (M := M) (1 : ℂ)) _set.val.left _set.val.right).mp (h_46 (M := M))).2 ((Litex.inInsert_iff (Litex.number (M := M) (1 : ℂ)) _set.val.right.val.element _set.val.right.val.tail _set.val.right.wd).mpr (Or.inl _same))))
      )
  )

theorem h_72 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_74 : Litex.IsSet _value_i5) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_75 : Litex.IsSet _value_i6) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_76 : Litex.IsSet _value_i7) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_77 : Litex.In _value_i8 _value_i5) (h_69 : ¬ Litex.In _value_i8 _value_i6) (h_70 : ¬ Litex.In _value_i8 _value_i7), (by
  let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.setMinus _value_i5 _value_i6);
  let _wd_1_1 := _value_i7;
  (Litex.setMinus _wd_1_0 _wd_1_1))
  exact Litex.In _value_i8 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_74 _Host_i6 _rep_i6 _value_i6 h_75 _Host_i7 _rep_i7 _value_i7 h_76 _Host_i8 _rep_i8 _value_i8 h_77 h_69 h_70
          have h_86 : Litex.IsSet _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  h_74
                )
            )
          have h_87 : Litex.IsSet _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  h_75
                )
            )
          have h_88 : Litex.IsSet _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  h_76
                )
            )
          have h_89 : Litex.In _value_i8 _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  h_77
                )
            )
          let _object_w12 := (let _wd_1_0 := (Litex.setMinus _value_i5 _value_i6);
          let _wd_1_1 := _value_i7;
          (Litex.setMinus _wd_1_0 _wd_1_1))

          have h_73 : (by
            let _atomic_wd_1_1 := _object_w12
            exact Litex.In _value_i8 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w12
                    exact (let _set := _atomic_wd_1_1; (Litex.inSetMinus_iff _value_i8 _set.val.left _set.val.right).mpr ⟨(by
                      let _atomic_wd_2_1 := (Litex.setMinus _value_i5 _value_i6)
                      exact (let _set := _atomic_wd_2_1; (Litex.inSetMinus_iff _value_i8 _set.val.left _set.val.right).mpr ⟨h_89, h_69⟩)), h_70⟩))
                )
            )

          have h_163 : Litex.In _value_i8 (Litex.setMinus _value_i5 _value_i6) :=
            (by
              litex_checked_step =>
                exact (
                  (let _set := _object_w12; ((Litex.inSetMinus_iff _value_i8 _set.val.left _set.val.right).mp h_73).1)
                )
            )

          have h_164 : ¬ Litex.In _value_i8 _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (let _set := _object_w12; ((Litex.inSetMinus_iff _value_i8 _set.val.left _set.val.right).mp h_73).2)
                )
            )
          exact (by
            let _atomic_wd_1_1 := _object_w12
            exact h_73)
        )
      )
  )

theorem h_185 : (by
  let _atomic_wd_1_1 := (let _wd_1_0 := (let _wd_1_0 := (Litex.R (M := M));
  let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  (Litex.setMinus _wd_1_0 _wd_1_1));
  let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0);
  (Litex.setMinus _wd_1_0 _wd_1_1))
  exact Litex.In (Litex.number (M := M) (1 : ℂ)) _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_186 : Litex.IsSet (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.isSet (Litex.R (M := M)))
                )
            )
          have h_187 : (by
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
          have h_188 : (by
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
          have h_189 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_66 (M := M))
                )
            )
          have h_190 : (by
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
                    exact (h_67 (M := M)))
                )
            )
          have h_191 : (by
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
          have h_192 : Litex.In (Litex.number (M := M) (1 : ℂ)) (let _wd_1_0 := (let _wd_1_0 := (Litex.R (M := M));
          let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (Litex.setMinus _wd_1_0 _wd_1_1));
          let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (Litex.setMinus _wd_1_0 _wd_1_1)) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_72 (M := M)) (Litex.R (M := M)) h_186 (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0) h_187 (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0) h_188 (Litex.number (M := M) (1 : ℂ)) h_189 h_190 h_191)
                )
            )
          have h_244 : Litex.In (Litex.number (M := M) (1 : ℂ)) (let _wd_1_0 := (Litex.R (M := M));
          let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (Litex.setMinus _wd_1_0 _wd_1_1)) :=
            (by
              litex_checked_step =>
                exact (
                  (let _set := (let _wd_1_0 := (let _wd_1_0 := (Litex.R (M := M));
                  let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.setMinus _wd_1_0 _wd_1_1));
                  let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.setMinus _wd_1_0 _wd_1_1)); ((Litex.inSetMinus_iff (Litex.number (M := M) (1 : ℂ)) _set.val.left _set.val.right).mp h_192).1)
                )
            )
          have h_245 : ¬ Litex.In (Litex.number (M := M) (1 : ℂ)) (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0) :=
            (by
              litex_checked_step =>
                exact (
                  (let _set := (let _wd_1_0 := (let _wd_1_0 := (Litex.R (M := M));
                  let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.setMinus _wd_1_0 _wd_1_1));
                  let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.setMinus _wd_1_0 _wd_1_1)); ((Litex.inSetMinus_iff (Litex.number (M := M) (1 : ℂ)) _set.val.left _set.val.right).mp h_192).2)
                )
            )
          have h_246 : ¬ Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (let _set := (let _wd_1_0 := (let _wd_1_0 := (Litex.R (M := M));
                  let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.setMinus _wd_1_0 _wd_1_1));
                  let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.setMinus _wd_1_0 _wd_1_1)); (fun _same => ((Litex.inSetMinus_iff (Litex.number (M := M) (1 : ℂ)) _set.val.left _set.val.right).mp h_192).2 ((Litex.inInsert_iff (Litex.number (M := M) (1 : ℂ)) _set.val.right.val.element _set.val.right.val.tail _set.val.right.wd).mpr (Or.inl _same))))
                )
            )
          exact (by
          let _atomic_wd_1_1 := (let _wd_1_0 := (let _wd_1_0 := (Litex.R (M := M));
          let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (Litex.setMinus _wd_1_0 _wd_1_1));
          let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0);
          (Litex.setMinus _wd_1_0 _wd_1_1))
          exact h_192)
        )
      )
  )

theorem h_255 : Litex.In (Litex.number (M := M) (1 : ℂ)) (let _wd_1_0 := (Litex.R (M := M));
let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0);
(Litex.setMinus _wd_1_0 _wd_1_1)) :=
  (by
    litex_complete =>
      exact (
        (let _set := (let _wd_1_0 := (let _wd_1_0 := (Litex.R (M := M));
        let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0);
        (Litex.setMinus _wd_1_0 _wd_1_1));
        let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0);
        (Litex.setMinus _wd_1_0 _wd_1_1)); ((Litex.inSetMinus_iff (Litex.number (M := M) (1 : ℂ)) _set.val.left _set.val.right).mp (h_185 (M := M))).1)
      )
  )

theorem h_256 : ¬ Litex.In (Litex.number (M := M) (1 : ℂ)) (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0) :=
  (by
    litex_complete =>
      exact (
        (let _set := (let _wd_1_0 := (let _wd_1_0 := (Litex.R (M := M));
        let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0);
        (Litex.setMinus _wd_1_0 _wd_1_1));
        let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0);
        (Litex.setMinus _wd_1_0 _wd_1_1)); ((Litex.inSetMinus_iff (Litex.number (M := M) (1 : ℂ)) _set.val.left _set.val.right).mp (h_185 (M := M))).2)
      )
  )

theorem h_257 : ¬ Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (let _set := (let _wd_1_0 := (let _wd_1_0 := (Litex.R (M := M));
        let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (0 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0);
        (Litex.setMinus _wd_1_0 _wd_1_1));
        let _wd_1_1 := (let _setElement_0 := (Litex.number (M := M) (2 : ℂ));
          let _setTail_1 := Litex.emptySet (M := M);
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0);
        (Litex.setMinus _wd_1_0 _wd_1_1)); (fun _same => ((Litex.inSetMinus_iff (Litex.number (M := M) (1 : ℂ)) _set.val.left _set.val.right).mp (h_185 (M := M))).2 ((Litex.inInsert_iff (Litex.number (M := M) (1 : ℂ)) _set.val.right.val.element _set.val.right.val.tail _set.val.right.wd).mpr (Or.inl _same))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_set_x5f_difference_x5f_theorem_x2f_statement_x2e_lit
