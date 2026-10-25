import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_difference_x5f_domains_x2f_statement_x2e_lit

universe u v1 v2 v3
variable {M : Litex.Semantics.{u}}

theorem h_5 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_30 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_31 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_32 : Litex.In _value_i3 (Litex.C (M := M))) (h_1 : Litex.Le _value_i1 _value_i2) (h_2 : (by
  let _atomic_wd_1_0 := (Litex.sub _value_i1 _value_i3 (M.real_subset_complex _ h_30) h_32)
  exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))) (h_3 : (by
  let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (M.real_subset_complex _ h_31) h_32)
  exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))), (by
  let _atomic_wd_1_0 := (Litex.sub _value_i1 _value_i3 (M.real_subset_complex _ h_30) h_32)
  let _atomic_wd_1_1 := (Litex.sub _value_i2 _value_i3 (M.real_subset_complex _ h_31) h_32)
  exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_30 _Host_i2 _rep_i2 _value_i2 h_31 _Host_i3 _rep_i3 _value_i3 h_32 h_1 h_2 h_3
          have h_4 : (by
            let _atomic_wd_1_0 := (Litex.sub _value_i1 _value_i3 (M.real_subset_complex _ h_30) h_32)
            let _atomic_wd_1_1 := (Litex.sub _value_i2 _value_i3 (M.real_subset_complex _ h_31) h_32)
            exact Litex.Le _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.sub _value_i1 _value_i3 (M.real_subset_complex _ h_30) h_32)
                    let _atomic_wd_1_1 := (Litex.sub _value_i2 _value_i3 (M.real_subset_complex _ h_31) h_32)
                    exact (by
                      let _litex_sub_left := _atomic_wd_1_0
                      let _litex_sub_right := _atomic_wd_1_1
                      exact Litex.subStructuralLeRight _litex_sub_left _litex_sub_right (by
                      let _atomic_wd_2_0 := _atomic_wd_1_0
                      exact h_2) h_1 (Litex.sameRefl _litex_sub_left.val.right)
                    ))
                )
            )
          exact h_4
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_difference_x5f_domains_x2f_statement_x2e_lit
