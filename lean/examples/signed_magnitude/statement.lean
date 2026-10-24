import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_signed_x5f_magnitude_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_6 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_19 : Litex.In _value_i1 (Litex.R (M := M))), (by
  let _object_w2 := (let _wd_1_0 := (Litex.sign _value_i1 h_19);
  let _wd_1_1 := (Litex.abs _value_i1 h_19);
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (M.real_subset_complex _ (by
      let _litex_abs := _atomic_wd_1_0
      exact Litex.absInR _litex_abs.val.arg _litex_abs.wd
    )))))
  let _object_w3 := (let _wd_1_0 := (_object_w2).val.right;
  let _wd_1_1 := (_object_w2).val.left;
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (M.real_subset_complex _ (by
      let _litex_abs := _atomic_wd_1_0
      exact Litex.absInR _litex_abs.val.arg _litex_abs.wd
    ))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0)))))
  let _object_w4 := (_object_w3).val.left
  let _object_w5 := (let _wd_1_0 := (_object_w3).val.right;
  let _wd_1_1 := _value_i1;
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0))) (M.real_subset_complex _ h_19)))
  let _object_w6 := (let _wd_1_0 := _value_i1;
  let _wd_1_1 := (_object_w5).val.left;
  (Litex.mul _wd_1_0 _wd_1_1 (M.real_subset_complex _ h_19) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0)))))
  exact (((by
    let _equal_wd_1_0 := _object_w2
    exact Litex.Same _equal_wd_1_0 _value_i1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w3
    exact Litex.Same _equal_wd_1_0 _value_i1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w4
    let _equal_wd_1_1 := _object_w5
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w6
    let _equal_wd_1_1 := _object_w4
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_1 := _object_w3
    exact Litex.Same _value_i1 _equal_wd_1_1)))))))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_19
          let _object_w2 := (let _wd_1_0 := (Litex.sign _value_i1 h_19);
          let _wd_1_1 := (Litex.abs _value_i1 h_19);
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (M.real_subset_complex _ (by
              let _litex_abs := _atomic_wd_1_0
              exact Litex.absInR _litex_abs.val.arg _litex_abs.wd
            )))))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w2
            exact Litex.Same _equal_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w2;
                  (show Litex.Same _equal_wd_1_0 _value_i1 from (Litex.signTimesAbs (_equal_wd_1_0).val.left true)))
                )
            )
          let _object_w3 := (let _wd_1_0 := (_object_w2).val.right;
          let _wd_1_1 := (_object_w2).val.left;
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (M.real_subset_complex _ (by
              let _litex_abs := _atomic_wd_1_0
              exact Litex.absInR _litex_abs.val.arg _litex_abs.wd
            ))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0)))))
          have h_2 : (by
            let _equal_wd_1_0 := _object_w3
            exact Litex.Same _equal_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w3;
                  (show Litex.Same _equal_wd_1_0 _value_i1 from (Litex.signTimesAbs (_equal_wd_1_0).val.right false)))
                )
            )
          let _object_w4 := (_object_w3).val.left
          let _object_w5 := (let _wd_1_0 := (_object_w3).val.right;
          let _wd_1_1 := _value_i1;
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0))) (M.real_subset_complex _ h_19)))
          have h_3 : (by
            let _equal_wd_1_0 := _object_w4
            let _equal_wd_1_1 := _object_w5
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w4;
                  let _equal_wd_1_1 := _object_w5;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.absEqualsSignTimes (_equal_wd_1_1).val.left true)))
                )
            )
          let _object_w6 := (let _wd_1_0 := _value_i1;
          let _wd_1_1 := (_object_w5).val.left;
          (Litex.mul _wd_1_0 _wd_1_1 (M.real_subset_complex _ h_19) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0)))))
          have h_4 : (by
            let _equal_wd_1_0 := _object_w6
            let _equal_wd_1_1 := _object_w4
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w6;
                  let _equal_wd_1_1 := _object_w4;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.absEqualsSignTimes (_equal_wd_1_0).val.right false).symm))
                )
            )
          have h_5 : (by
            let _equal_wd_1_1 := _object_w3
            exact Litex.Same _value_i1 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (h_2).symm
                )
            )
          exact (And.intro h_1 (And.intro h_2 (And.intro h_3 (And.intro h_4 h_5))))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_signed_x5f_magnitude_x2f_statement_x2e_lit
