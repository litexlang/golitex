import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_weak_x5f_additive_x5f_upper_x5f_bounds_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6
variable {M : Litex.Semantics.{u}}

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_17 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_18 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_19 : Litex.In _value_i3 (Litex.R (M := M))) (h_1 : Litex.Le _value_i2 _value_i1) (h_2 : Litex.Le _value_i3 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_w3 := (Litex.add _value_i2 _value_i3 (M.real_subset_complex _ h_18) (M.real_subset_complex _ h_19))
  exact (by
    let _atomic_wd_1_0 := _object_w3
    exact Litex.Le _atomic_wd_1_0 _value_i1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_17 _Host_i2 _rep_i2 _value_i2 h_18 _Host_i3 _rep_i3 _value_i3 h_19 h_1 h_2
          let _object_w3 := (Litex.add _value_i2 _value_i3 (M.real_subset_complex _ h_18) (M.real_subset_complex _ h_19))
          have h_3 : (by
            let _atomic_wd_1_0 := _object_w3
            exact Litex.Le _atomic_wd_1_0 _value_i1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w3
                    exact (Litex.addLeOfLeOfNonpos _atomic_wd_1_0 _value_i1 h_1 h_2))
                )
            )
          exact h_3
        )
      )
  )

theorem h_1588 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_1602 : Litex.In _value_i4 (Litex.R (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_1603 : Litex.In _value_i5 (Litex.R (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_1604 : Litex.In _value_i6 (Litex.R (M := M))) (h_1585 : Litex.Le _value_i6 _value_i4) (h_1586 : Litex.Le _value_i5 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_w6 := (Litex.add _value_i5 _value_i6 (M.real_subset_complex _ h_1603) (M.real_subset_complex _ h_1604))
  exact (by
    let _atomic_wd_1_0 := _object_w6
    exact Litex.Le _atomic_wd_1_0 _value_i4)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_1602 _Host_i5 _rep_i5 _value_i5 h_1603 _Host_i6 _rep_i6 _value_i6 h_1604 h_1585 h_1586
          let _object_w6 := (Litex.add _value_i5 _value_i6 (M.real_subset_complex _ h_1603) (M.real_subset_complex _ h_1604))
          have h_1587 : (by
            let _atomic_wd_1_0 := _object_w6
            exact Litex.Le _atomic_wd_1_0 _value_i4) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w6
                    exact (Litex.addLeOfLeOfNonposSwap _atomic_wd_1_0 _value_i4 h_1585 h_1586))
                )
            )
          exact h_1587
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_weak_x5f_additive_x5f_upper_x5f_bounds_x2f_statement_x2e_lit
