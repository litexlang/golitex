import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_mixed_x5f_strict_x5f_sum_x5f_bounds_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6 v7 v8
variable {M : Litex.Semantics.{u}}

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_17 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_18 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_19 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_20 : Litex.In _value_i4 (Litex.R (M := M))) (h_1 : Litex.Lt _value_i1 _value_i2) (h_2 : Litex.Le _value_i3 _value_i4), (by
  let _object_w2 := (Litex.add _value_i1 _value_i3 (M.real_subset_complex _ h_17) (M.real_subset_complex _ h_19))
  let _object_w3 := (Litex.add _value_i2 _value_i4 (M.real_subset_complex _ h_18) (M.real_subset_complex _ h_20))
  exact (by
    let _atomic_wd_1_0 := _object_w2
    let _atomic_wd_1_1 := _object_w3
    exact Litex.Lt _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_17 _Host_i2 _rep_i2 _value_i2 h_18 _Host_i3 _rep_i3 _value_i3 h_19 _Host_i4 _rep_i4 _value_i4 h_20 h_1 h_2
          let _object_w2 := (Litex.add _value_i1 _value_i3 (M.real_subset_complex _ h_17) (M.real_subset_complex _ h_19))
          let _object_w3 := (Litex.add _value_i2 _value_i4 (M.real_subset_complex _ h_18) (M.real_subset_complex _ h_20))
          have h_3 : (by
            let _atomic_wd_1_0 := _object_w2
            let _atomic_wd_1_1 := _object_w3
            exact Litex.Lt _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w2
                    let _atomic_wd_1_1 := _object_w3
                    exact (Litex.addLtAddOfLtOfLe _atomic_wd_1_0 _atomic_wd_1_1 h_1 h_2))
                )
            )
          exact h_3
        )
      )
  )

theorem h_1607 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_1621 : Litex.In _value_i5 (Litex.R (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_1622 : Litex.In _value_i6 (Litex.R (M := M))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_1623 : Litex.In _value_i7 (Litex.R (M := M))) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_1624 : Litex.In _value_i8 (Litex.R (M := M))) (h_1604 : Litex.Le _value_i5 _value_i6) (h_1605 : Litex.Lt _value_i7 _value_i8), (by
  let _object_w5 := (Litex.add _value_i5 _value_i7 (M.real_subset_complex _ h_1621) (M.real_subset_complex _ h_1623))
  let _object_w6 := (Litex.add _value_i6 _value_i8 (M.real_subset_complex _ h_1622) (M.real_subset_complex _ h_1624))
  exact (by
    let _atomic_wd_1_0 := _object_w5
    let _atomic_wd_1_1 := _object_w6
    exact Litex.Lt _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_1621 _Host_i6 _rep_i6 _value_i6 h_1622 _Host_i7 _rep_i7 _value_i7 h_1623 _Host_i8 _rep_i8 _value_i8 h_1624 h_1604 h_1605
          let _object_w5 := (Litex.add _value_i5 _value_i7 (M.real_subset_complex _ h_1621) (M.real_subset_complex _ h_1623))
          let _object_w6 := (Litex.add _value_i6 _value_i8 (M.real_subset_complex _ h_1622) (M.real_subset_complex _ h_1624))
          have h_1606 : (by
            let _atomic_wd_1_0 := _object_w5
            let _atomic_wd_1_1 := _object_w6
            exact Litex.Lt _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w5
                    let _atomic_wd_1_1 := _object_w6
                    exact (Litex.addLtAddOfLeOfLt _atomic_wd_1_0 _atomic_wd_1_1 h_1604 h_1605))
                )
            )
          exact h_1606
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_mixed_x5f_strict_x5f_sum_x5f_bounds_x2f_statement_x2e_lit
