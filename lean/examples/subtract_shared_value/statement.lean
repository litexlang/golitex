import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_subtract_x5f_shared_x5f_value_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_17 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_18 : Litex.In _value_i3 (Litex.R (M := M))) (h_1 : Litex.Le _value_i1 _value_i2), (by
  let _object_w2 := (Litex.sub _value_i1 _value_i3 (M.real_subset_complex _ h_16) (M.real_subset_complex _ h_18))
  let _object_w3 := (Litex.sub _value_i2 _value_i3 (M.real_subset_complex _ h_17) (M.real_subset_complex _ h_18))
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
          let _object_w2 := (Litex.sub _value_i1 _value_i3 (M.real_subset_complex _ h_16) (M.real_subset_complex _ h_18))
          let _object_w3 := (Litex.sub _value_i2 _value_i3 (M.real_subset_complex _ h_17) (M.real_subset_complex _ h_18))
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
                      exact Litex.subStructuralLeRight _litex_sub_left _litex_sub_right (by
                      let _atomic_wd_2_0 := _atomic_wd_1_0
                      exact (Litex.subInR _value_i1 _value_i3 h_16 h_18)) h_1 (Litex.sameRefl _litex_sub_left.val.right)
                    ))
                )
            )
          exact h_2
        )
      )
  )

theorem h_2428 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_2442 : Litex.In _value_i4 (Litex.R (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_2443 : Litex.In _value_i5 (Litex.R (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_2444 : Litex.In _value_i6 (Litex.R (M := M))) (h_2426 : Litex.Lt _value_i4 _value_i5), (by
  let _object_w5 := (Litex.sub _value_i4 _value_i6 (M.real_subset_complex _ h_2442) (M.real_subset_complex _ h_2444))
  let _object_w6 := (Litex.sub _value_i5 _value_i6 (M.real_subset_complex _ h_2443) (M.real_subset_complex _ h_2444))
  exact (by
    let _atomic_wd_1_0 := _object_w5
    let _atomic_wd_1_1 := _object_w6
    exact Litex.Lt _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_2442 _Host_i5 _rep_i5 _value_i5 h_2443 _Host_i6 _rep_i6 _value_i6 h_2444 h_2426
          let _object_w5 := (Litex.sub _value_i4 _value_i6 (M.real_subset_complex _ h_2442) (M.real_subset_complex _ h_2444))
          let _object_w6 := (Litex.sub _value_i5 _value_i6 (M.real_subset_complex _ h_2443) (M.real_subset_complex _ h_2444))
          have h_2427 : (by
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
                      exact Litex.subStructuralLtRight _litex_sub_left _litex_sub_right (by
                      let _atomic_wd_2_0 := _atomic_wd_1_0
                      exact (Litex.subInR _value_i4 _value_i6 h_2442 h_2444)) h_2426 (Litex.sameRefl _litex_sub_left.val.right)
                    ))
                )
            )
          exact h_2427
        )
      )
  )

theorem h_3698 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_3711 : Litex.In _value_i7 (Litex.R (M := M))) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_3712 : Litex.In _value_i8 (Litex.R (M := M))) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_3713 : Litex.In _value_i9 (Litex.R (M := M))) {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_3714 : Litex.In _value_i10 (Litex.R (M := M))) (h_3696 : Litex.Le _value_i7 _value_i8), (by
  let _object_w8 := (let _wd_1_0 := _value_i7;
  let _wd_1_1 := (Litex.add _value_i9 _value_i10 (M.real_subset_complex _ h_3713) (M.real_subset_complex _ h_3714));
  (Litex.sub _wd_1_0 _wd_1_1 (M.real_subset_complex _ h_3711) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.addInC _value_i9 _value_i10 (M.real_subset_complex _ h_3713) (M.real_subset_complex _ h_3714)))))
  let _object_w9 := (let _wd_1_0 := _value_i8;
  let _wd_1_1 := (Litex.add _value_i9 _value_i10 (M.real_subset_complex _ h_3713) (M.real_subset_complex _ h_3714));
  (Litex.sub _wd_1_0 _wd_1_1 (M.real_subset_complex _ h_3712) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.addInC _value_i9 _value_i10 (M.real_subset_complex _ h_3713) (M.real_subset_complex _ h_3714)))))
  exact (by
    let _atomic_wd_1_0 := _object_w8
    let _atomic_wd_1_1 := _object_w9
    exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_3711 _Host_i8 _rep_i8 _value_i8 h_3712 _Host_i9 _rep_i9 _value_i9 h_3713 _Host_i10 _rep_i10 _value_i10 h_3714 h_3696
          let _object_w8 := (let _wd_1_0 := _value_i7;
          let _wd_1_1 := (Litex.add _value_i9 _value_i10 (M.real_subset_complex _ h_3713) (M.real_subset_complex _ h_3714));
          (Litex.sub _wd_1_0 _wd_1_1 (M.real_subset_complex _ h_3711) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.addInC _value_i9 _value_i10 (M.real_subset_complex _ h_3713) (M.real_subset_complex _ h_3714)))))
          let _object_w9 := (let _wd_1_0 := _value_i8;
          let _wd_1_1 := (Litex.add _value_i9 _value_i10 (M.real_subset_complex _ h_3713) (M.real_subset_complex _ h_3714));
          (Litex.sub _wd_1_0 _wd_1_1 (M.real_subset_complex _ h_3712) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.addInC _value_i9 _value_i10 (M.real_subset_complex _ h_3713) (M.real_subset_complex _ h_3714)))))
          have h_3697 : (by
            let _atomic_wd_1_0 := _object_w8
            let _atomic_wd_1_1 := _object_w9
            exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w8
                    let _atomic_wd_1_1 := _object_w9
                    exact (by
                      let _litex_sub_left := _atomic_wd_1_0
                      let _litex_sub_right := _atomic_wd_1_1
                      exact Litex.subStructuralLeRight _litex_sub_left _litex_sub_right (by
                      let _atomic_wd_2_0 := _atomic_wd_1_0
                      exact (Litex.subInR _value_i7 (_atomic_wd_2_0).val.right h_3711 (Litex.addInR _value_i9 _value_i10 h_3713 h_3714))) h_3696 (Litex.sameRefl _litex_sub_left.val.right)
                    ))
                )
            )
          exact h_3697
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_subtract_x5f_shared_x5f_value_x2f_statement_x2e_lit
