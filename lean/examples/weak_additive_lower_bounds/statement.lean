import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_weak_x5f_additive_x5f_lower_x5f_bounds_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6
variable {M : Litex.Semantics.{u}}

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_17 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_18 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_19 : Litex.In _value_i3 (Litex.R (M := M))) (h_1 : Litex.Le _value_i1 _value_i2) (h_2 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3), (by
  let _object_w3 := (Litex.add _value_i2 _value_i3 (M.real_subset_complex _ h_18) (M.real_subset_complex _ h_19))
  exact (by
    let _atomic_wd_1_1 := _object_w3
    exact Litex.Le _value_i1 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_17 _Host_i2 _rep_i2 _value_i2 h_18 _Host_i3 _rep_i3 _value_i3 h_19 h_1 h_2
          let _object_w3 := (Litex.add _value_i2 _value_i3 (M.real_subset_complex _ h_18) (M.real_subset_complex _ h_19))
          have h_3 : (by
            let _atomic_wd_1_1 := _object_w3
            exact Litex.Le _value_i1 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w3
                    exact (Litex.leAddOfLeOfNonneg _value_i1 _atomic_wd_1_1 h_1 h_2))
                )
            )
          exact h_3
        )
      )
  )

theorem h_1558 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_1572 : Litex.In _value_i4 (Litex.R (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_1573 : Litex.In _value_i5 (Litex.R (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_1574 : Litex.In _value_i6 (Litex.R (M := M))) (h_1555 : Litex.Le _value_i4 _value_i6) (h_1556 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i5), (by
  let _object_w6 := (Litex.add _value_i5 _value_i6 (M.real_subset_complex _ h_1573) (M.real_subset_complex _ h_1574))
  exact (by
    let _atomic_wd_1_1 := _object_w6
    exact Litex.Le _value_i4 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_1572 _Host_i5 _rep_i5 _value_i5 h_1573 _Host_i6 _rep_i6 _value_i6 h_1574 h_1555 h_1556
          let _object_w6 := (Litex.add _value_i5 _value_i6 (M.real_subset_complex _ h_1573) (M.real_subset_complex _ h_1574))
          have h_1557 : (by
            let _atomic_wd_1_1 := _object_w6
            exact Litex.Le _value_i4 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w6
                    exact (Litex.leAddOfLeOfNonnegSwap _value_i4 _atomic_wd_1_1 h_1555 h_1556))
                )
            )
          exact h_1557
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_weak_x5f_additive_x5f_lower_x5f_bounds_x2f_statement_x2e_lit
