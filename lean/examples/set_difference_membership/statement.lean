import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_set_x5f_difference_x5f_membership_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6 v7 v8 v9
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_17 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_18 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_19 : Litex.In _value_i3 (Litex.R (M := M))) (h_1 : Litex.In _value_i3 _value_i1) (h_2 : ¬ Litex.In _value_i3 _value_i2), (by
  let _object_w2 := (Litex.setMinus _value_i1 _value_i2)
  exact (by
    let _atomic_wd_1_1 := _object_w2
    exact Litex.In _value_i3 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_17 _Host_i2 _rep_i2 _value_i2 h_18 _Host_i3 _rep_i3 _value_i3 h_19 h_1 h_2
          let _object_w2 := (Litex.setMinus _value_i1 _value_i2)
          have h_3 : (by
            let _atomic_wd_1_1 := _object_w2
            exact Litex.In _value_i3 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w2
                    exact (let _set := _atomic_wd_1_1; (Litex.inSetMinus_iff _value_i3 _set.val.left _set.val.right).mpr ⟨h_1, h_2⟩))
                )
            )
          have h_52 : Litex.In _value_i3 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (let _set := _object_w2; ((Litex.inSetMinus_iff _value_i3 _set.val.left _set.val.right).mp h_3).1)
                )
            )
          have h_53 : ¬ Litex.In _value_i3 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (let _set := _object_w2; ((Litex.inSetMinus_iff _value_i3 _set.val.left _set.val.right).mp h_3).2)
                )
            )
          exact h_3
        )
      )
  )

theorem h_56 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_58 : Litex.IsSet _value_i4) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_59 : Litex.IsSet _value_i5) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_60 : Litex.In _value_i6 (Litex.setMinus _value_i4 _value_i5)), ((Litex.In _value_i6 _value_i4) ∧ (¬ Litex.In _value_i6 _value_i5)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_58 _Host_i5 _rep_i5 _value_i5 h_59 _Host_i6 _rep_i6 _value_i6 h_60
          have h_61 : Litex.In _value_i6 _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (let _set := (Litex.setMinus _value_i4 _value_i5); ((Litex.inSetMinus_iff _value_i6 _set.val.left _set.val.right).mp h_60).1)
                )
            )
          have h_62 : ¬ Litex.In _value_i6 _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (let _set := (Litex.setMinus _value_i4 _value_i5); ((Litex.inSetMinus_iff _value_i6 _set.val.left _set.val.right).mp h_60).2)
                )
            )
          have h_54 : Litex.In _value_i6 _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  h_61
                )
            )
          have h_55 : ¬ Litex.In _value_i6 _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  h_62
                )
            )
          exact (And.intro h_54 h_55)
        )
      )
  )

theorem h_78 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_92 : Litex.IsSet _value_i7) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_93 : Litex.In _value_i8 (Litex.R (M := M))) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_94 : Litex.In _value_i9 (let _wd_1_0 := _value_i7;
let _wd_1_1 := (let _setElement_0 := _value_i8;
  let _setTail_1 := Litex.emptySet (M := M);
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0);
(Litex.setMinus _wd_1_0 _wd_1_1))), ((¬ Litex.Same _value_i9 _value_i8) ∧ (((Litex.In _value_i9 _value_i7) ∧ ((by
  let _atomic_wd_1_1 := (let _setElement_0 := _value_i8;
    let _setTail_1 := Litex.emptySet (M := M);
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact ¬ Litex.In _value_i9 _atomic_wd_1_1))))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_92 _Host_i8 _rep_i8 _value_i8 h_93 _Host_i9 _rep_i9 _value_i9 h_94
          have h_95 : Litex.In _value_i9 _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  (let _set := (let _wd_1_0 := _value_i7;
                  let _wd_1_1 := (let _setElement_0 := _value_i8;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.setMinus _wd_1_0 _wd_1_1)); ((Litex.inSetMinus_iff _value_i9 _set.val.left _set.val.right).mp h_94).1)
                )
            )
          have h_96 : ¬ Litex.In _value_i9 (let _setElement_0 := _value_i8;
            let _setTail_1 := Litex.emptySet (M := M);
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0) :=
            (by
              litex_checked_step =>
                exact (
                  (let _set := (let _wd_1_0 := _value_i7;
                  let _wd_1_1 := (let _setElement_0 := _value_i8;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.setMinus _wd_1_0 _wd_1_1)); ((Litex.inSetMinus_iff _value_i9 _set.val.left _set.val.right).mp h_94).2)
                )
            )
          have h_97 : ¬ Litex.Same _value_i9 _value_i8 :=
            (by
              litex_checked_step =>
                exact (
                  (let _set := (let _wd_1_0 := _value_i7;
                  let _wd_1_1 := (let _setElement_0 := _value_i8;
                    let _setTail_1 := Litex.emptySet (M := M);
                    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                    _setTail_0);
                  (Litex.setMinus _wd_1_0 _wd_1_1)); (fun _same => ((Litex.inSetMinus_iff _value_i9 _set.val.left _set.val.right).mp h_94).2 ((Litex.inInsert_iff _value_i9 _set.val.right.val.element _set.val.right.val.tail _set.val.right.wd).mpr (Or.inl _same))))
                )
            )
          have h_75 : ¬ Litex.Same _value_i9 _value_i8 :=
            (by
              litex_checked_step =>
                exact (
                  h_97
                )
            )
          have h_76 : Litex.In _value_i9 _value_i7 :=
            (by
              litex_checked_step =>
                exact (
                  h_95
                )
            )
          have h_77 : (by
            let _atomic_wd_1_1 := (let _setElement_0 := _value_i8;
              let _setTail_1 := Litex.emptySet (M := M);
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)
            exact ¬ Litex.In _value_i9 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (let _setElement_0 := _value_i8;
                      let _setTail_1 := Litex.emptySet (M := M);
                      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInEmpty _setElement_0);
                      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
                      _setTail_0)
                    exact h_96)
                )
            )
          exact (And.intro h_75 (And.intro h_76 h_77))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_set_x5f_difference_x5f_membership_x2f_statement_x2e_lit
