import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_nonmembership_x2f_statement_x2e_lit

universe u v1 v2 v3 v4
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

noncomputable def _object_w2 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
  let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
  let _setElement_2 := (Litex.number (M := M) (3 : ℂ));
  let _setTail_3 := Litex.emptySet (M := M);
  let _setFresh_2 : ¬ Litex.In _setElement_2 _setTail_3 := (Litex.notInEmpty _setElement_2);
  let _setTail_2 := Litex.insert _setElement_2 _setTail_3 _setFresh_2;
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInInsert _setElement_1 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (2 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_1));
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInInsert _setElement_0 _setElement_2 _setTail_3 _setFresh_2 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (1 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0)));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0)

theorem h_1 : (by
  let _atomic_wd_1_1 := (_object_w2 (M := M))
  exact ¬ Litex.In (Litex.number (M := M) (4 : ℂ)) _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_1 := (_object_w2 (M := M))
          exact (by
            let _set := _atomic_wd_1_1
            exact (Litex.notInInsert (Litex.number (M := M) (4 : ℂ)) _set.val.element _set.val.tail _set.wd (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (4 : ℂ) (1 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num)) (Litex.notInInsert (Litex.number (M := M) (4 : ℂ)) _set.val.tail.val.element _set.val.tail.val.tail _set.val.tail.wd (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (4 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInInsert (Litex.number (M := M) (4 : ℂ)) _set.val.tail.val.tail.val.element _set.val.tail.val.tail.val.tail _set.val.tail.val.tail.wd (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (4 : ℂ) (3 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)) (Litex.notInEmpty (Litex.number (M := M) (4 : ℂ))))))))
      )
  )

theorem h_11 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_24 : Litex.In _value_i1 (Litex.R (M := M))) (h_8 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (1 : ℂ))) (h_9 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (2 : ℂ))), (by
  let _object_w6 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
    let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0)
  exact (by
    let _atomic_wd_1_1 := _object_w6
    exact ¬ Litex.In _value_i1 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_24 h_8 h_9
          let _object_w6 := (let _setElement_0 := (Litex.number (M := M) (1 : ℂ));
            let _setElement_1 := (Litex.number (M := M) (2 : ℂ));
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (1 : ℂ) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num)) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0)
          have h_10 : (by
            let _atomic_wd_1_1 := _object_w6
            exact ¬ Litex.In _value_i1 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w6
                    exact (by
                      let _set := _atomic_wd_1_1
                      exact (Litex.notInInsert _value_i1 _set.val.element _set.val.tail _set.wd h_8 (Litex.notInInsert _value_i1 _set.val.tail.val.element _set.val.tail.val.tail _set.val.tail.wd h_9 (Litex.notInEmpty _value_i1)))))
                )
            )
          exact h_10
        )
      )
  )

theorem h_54 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_79 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_80 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_81 : Litex.In _value_i4 (Litex.R (M := M))) (h_50 : Litex.In _value_i3 _value_i2) (h_51 : ¬ Litex.In _value_i4 _value_i2), ((¬ Litex.Same _value_i3 _value_i4) ∧ (¬ Litex.Same _value_i4 _value_i3)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_79 _Host_i3 _rep_i3 _value_i3 h_80 _Host_i4 _rep_i4 _value_i4 h_81 h_50 h_51
          have h_52 : ¬ Litex.Same _value_i3 _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.notSameOfMembership _value_i3 _value_i4 _value_i2 h_50 h_51)
                )
            )
          have h_53 : ¬ Litex.Same _value_i4 _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_same => h_52 _litex_same.symm)
                )
            )
          exact (And.intro h_52 h_53)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_nonmembership_x2f_statement_x2e_lit
