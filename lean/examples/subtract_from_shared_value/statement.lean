import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_subtract_x5f_from_x5f_shared_x5f_value_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_17 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_18 : Litex.In _value_i3 (Litex.R (M := M))) (h_1 : Litex.Le _value_i1 _value_i2), (by
  let _object_w2 := (Litex.sub _value_i3 _value_i2 (M.real_subset_complex _ h_18) (M.real_subset_complex _ h_17))
  let _object_w3 := (Litex.sub _value_i3 _value_i1 (M.real_subset_complex _ h_18) (M.real_subset_complex _ h_16))
  exact (by
    let _atomic_wd_1_0 := _object_w2
    let _atomic_wd_1_1 := _object_w3
    exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_16 _Host_i2 _rep_i2 _value_i2 h_17 _Host_i3 _rep_i3 _value_i3 h_18 h_1
          let _object_w2 := (Litex.sub _value_i3 _value_i2 (M.real_subset_complex _ h_18) (M.real_subset_complex _ h_17))
          let _object_w3 := (Litex.sub _value_i3 _value_i1 (M.real_subset_complex _ h_18) (M.real_subset_complex _ h_16))
          have h_2 : (by
            let _atomic_wd_1_0 := _object_w2
            let _atomic_wd_1_1 := _object_w3
            exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w2
                    let _atomic_wd_1_1 := _object_w3
                    exact (by
                      let _litex_sub_left := _atomic_wd_1_0
                      let _litex_sub_right := _atomic_wd_1_1
                      exact Litex.subStructuralLeLeft _litex_sub_left _litex_sub_right (by
                      let _atomic_wd_2_0 := _atomic_wd_1_0
                      exact (Litex.subInR _value_i3 _value_i2 h_18 h_17)) h_1 (Litex.sameRefl _litex_sub_left.val.left)
                    ))
                )
            )
          exact h_2
        )
      )
  )

theorem h_2424 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_2438 : Litex.In _value_i4 (Litex.R (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_2439 : Litex.In _value_i5 (Litex.R (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_2440 : Litex.In _value_i6 (Litex.R (M := M))) (h_2422 : Litex.Lt _value_i4 _value_i5), (by
  let _object_w5 := (Litex.sub _value_i6 _value_i5 (M.real_subset_complex _ h_2440) (M.real_subset_complex _ h_2439))
  let _object_w6 := (Litex.sub _value_i6 _value_i4 (M.real_subset_complex _ h_2440) (M.real_subset_complex _ h_2438))
  exact (by
    let _atomic_wd_1_0 := _object_w5
    let _atomic_wd_1_1 := _object_w6
    exact Litex.Lt _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_2438 _Host_i5 _rep_i5 _value_i5 h_2439 _Host_i6 _rep_i6 _value_i6 h_2440 h_2422
          let _object_w5 := (Litex.sub _value_i6 _value_i5 (M.real_subset_complex _ h_2440) (M.real_subset_complex _ h_2439))
          let _object_w6 := (Litex.sub _value_i6 _value_i4 (M.real_subset_complex _ h_2440) (M.real_subset_complex _ h_2438))
          have h_2423 : (by
            let _atomic_wd_1_0 := _object_w5
            let _atomic_wd_1_1 := _object_w6
            exact Litex.Lt _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w5
                    let _atomic_wd_1_1 := _object_w6
                    exact (by
                      let _litex_sub_left := _atomic_wd_1_0
                      let _litex_sub_right := _atomic_wd_1_1
                      exact Litex.subStructuralLtLeft _litex_sub_left _litex_sub_right (by
                      let _atomic_wd_2_0 := _atomic_wd_1_0
                      exact (Litex.subInR _value_i6 _value_i5 h_2440 h_2439)) h_2422 (Litex.sameRefl _litex_sub_left.val.left)
                    ))
                )
            )
          exact h_2423
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_subtract_x5f_from_x5f_shared_x5f_value_x2f_statement_x2e_lit
