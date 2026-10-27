import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_symmetric_x5f_difference_x5f_identities_x2f_statement_x2e_lit

universe u v1 v2 v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_3 : Litex.IsSet _value_i1), (by
  let _object_w1 := (Litex.symmetricDifference _value_i1 _value_i1)
  let _object_w2 := (let _setTail_0 := Litex.emptySet (M := M);
    _setTail_0)
  exact (by
    let _equal_wd_1_0 := _object_w1
    let _equal_wd_1_1 := _object_w2
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_3
          let _object_w1 := (Litex.symmetricDifference _value_i1 _value_i1)
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
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (let _litex_set := _equal_wd_1_0; (Litex.symmetricDifferenceSelf _litex_set.val.left))))
                )
            )
          exact h_1
        )
      )
  )

theorem h_16 : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_17 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_18 : Litex.IsSet _value_i3), (by
  let _object_w3 := (Litex.symmetricDifference _value_i2 _value_i3)
  let _object_w4 := (let _wd_1_0 := (Litex.setMinus _value_i2 _value_i3);
  let _wd_1_1 := (Litex.setMinus _value_i3 _value_i2);
  (Litex.union _wd_1_0 _wd_1_1))
  exact (by
    let _equal_wd_1_0 := _object_w3
    let _equal_wd_1_1 := _object_w4
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i2 _rep_i2 _value_i2 h_17 _Host_i3 _rep_i3 _value_i3 h_18
          let _object_w3 := (Litex.symmetricDifference _value_i2 _value_i3)
          let _object_w4 := (let _wd_1_0 := (Litex.setMinus _value_i2 _value_i3);
          let _wd_1_1 := (Litex.setMinus _value_i3 _value_i2);
          (Litex.union _wd_1_0 _wd_1_1))
          have h_15 : (by
            let _equal_wd_1_0 := _object_w3
            let _equal_wd_1_1 := _object_w4
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w3;
                  let _equal_wd_1_1 := _object_w4;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (let _litex_set := _equal_wd_1_0; (Litex.symmetricDifferenceDefinition _litex_set.val.left _litex_set.val.right))))
                )
            )
          exact h_15
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_symmetric_x5f_difference_x5f_identities_x2f_statement_x2e_lit
