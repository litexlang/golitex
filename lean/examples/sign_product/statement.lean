import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_sign_x5f_product_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_29 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_30 : Litex.In _value_i2 (Litex.R (M := M))), (by
  let _object_w2 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i2 (M.real_subset_complex _ h_29) (M.real_subset_complex _ h_30));
  (Litex.sign _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.mulInR _value_i1 _value_i2 h_29 h_30))))
  let _object_w3 := (let _wd_1_0 := (Litex.sign _value_i1 h_29);
  let _wd_1_1 := (Litex.sign _value_i2 h_30);
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0)))))
  let _object_w4 := (let _wd_1_0 := (_object_w3).val.right;
  let _wd_1_1 := (_object_w3).val.left;
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0)))))
  let _object_w5 := (let _wd_1_0 := (Litex.mul _value_i2 _value_i1 (M.real_subset_complex _ h_30) (M.real_subset_complex _ h_29));
  (Litex.sign _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.mulInR _value_i2 _value_i1 h_30 h_29))))
  exact (((by
    let _equal_wd_1_0 := _object_w2
    let _equal_wd_1_1 := _object_w3
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w2
    let _equal_wd_1_1 := _object_w4
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w3
    let _equal_wd_1_1 := _object_w5
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_29 _Host_i2 _rep_i2 _value_i2 h_30
          let _object_w2 := (let _wd_1_0 := (Litex.mul _value_i1 _value_i2 (M.real_subset_complex _ h_29) (M.real_subset_complex _ h_30));
          (Litex.sign _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.mulInR _value_i1 _value_i2 h_29 h_30))))
          let _object_w3 := (let _wd_1_0 := (Litex.sign _value_i1 h_29);
          let _wd_1_1 := (Litex.sign _value_i2 h_30);
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0)))))
          have h_1 : (by
            let _equal_wd_1_0 := _object_w2
            let _equal_wd_1_1 := _object_w3
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w2;
                  let _equal_wd_1_1 := _object_w3;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.signProduct (_equal_wd_1_1).val.left (_equal_wd_1_1).val.right false)))
                )
            )
          let _object_w4 := (let _wd_1_0 := (_object_w3).val.right;
          let _wd_1_1 := (_object_w3).val.left;
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0)))))
          have h_2 : (by
            let _equal_wd_1_0 := _object_w2
            let _equal_wd_1_1 := _object_w4
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w2;
                  let _equal_wd_1_1 := _object_w4;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.signProduct (_equal_wd_1_1).val.left (_equal_wd_1_1).val.right true)))
                )
            )
          let _object_w5 := (let _wd_1_0 := (Litex.mul _value_i2 _value_i1 (M.real_subset_complex _ h_30) (M.real_subset_complex _ h_29));
          (Litex.sign _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.mulInR _value_i2 _value_i1 h_30 h_29))))
          have h_3 : (by
            let _equal_wd_1_0 := _object_w3
            let _equal_wd_1_1 := _object_w5
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.signProduct (_object_w4).val.right (_object_w4).val.left true).symm
                )
            )
          exact (And.intro h_1 (And.intro h_2 h_3))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_sign_x5f_product_x2f_statement_x2e_lit
