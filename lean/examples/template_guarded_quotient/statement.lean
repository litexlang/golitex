import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_template_x5f_guarded_x5f_quotient_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

noncomputable def _template_i3 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_3 : Litex.In _value_i2 (Litex.R (M := M))) (h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))) : Litex.Obj (M := M) M.Value := by
  let _object_i3 := (Litex.div _value_i1 _value_i2 (M.real_subset_complex _ h_2) (M.real_subset_complex _ h_3) h_1)
  have h_86 : Litex.In _object_i3 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := (Litex.div _value_i1 _value_i2 (M.real_subset_complex _ h_2) (M.real_subset_complex _ h_3) h_1)
            exact (Litex.divInR _value_i1 _value_i2 h_2 h_3 (_atomic_wd_1_0).wd.2.2))
        )
    )
  have h_87 : Litex.Same _object_i3 _object_i3 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.sameRefl (Litex.div _value_i1 _value_i2 (M.real_subset_complex _ h_2) (M.real_subset_complex _ h_3) h_1))
        )
    )
  exact Litex.semanticObject (Litex.denote _object_i3) (Litex.isSet _object_i3)

theorem h_89 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_3 : Litex.In _value_i2 (Litex.R (M := M))) (h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))), Litex.In ((_template_i3 (M := M)) _value_i1 h_2 _value_i2 h_3 h_1) (Litex.R (M := M)) := by
  intro _Host_i1 _rep_i1 _value_i1 h_2 _Host_i2 _rep_i2 _value_i2 h_3 h_1
  let _object_i3 := (Litex.div _value_i1 _value_i2 (M.real_subset_complex _ h_2) (M.real_subset_complex _ h_3) h_1)
  have h_86 : Litex.In _object_i3 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := (Litex.div _value_i1 _value_i2 (M.real_subset_complex _ h_2) (M.real_subset_complex _ h_3) h_1)
            exact (Litex.divInR _value_i1 _value_i2 h_2 h_3 (_atomic_wd_1_0).wd.2.2))
        )
    )
  have h_87 : Litex.Same _object_i3 _object_i3 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.sameRefl (Litex.div _value_i1 _value_i2 (M.real_subset_complex _ h_2) (M.real_subset_complex _ h_3) h_1))
        )
    )
  exact h_86

theorem h_91 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_2 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_3 : Litex.In _value_i2 (Litex.R (M := M))) (h_1 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))), (by
  let _object_i3 := (Litex.div _value_i1 _value_i2 (M.real_subset_complex _ h_2) (M.real_subset_complex _ h_3) h_1)
  exact Litex.Same ((_template_i3 (M := M)) _value_i1 h_2 _value_i2 h_3 h_1) _object_i3
) := by
  intro _Host_i1 _rep_i1 _value_i1 h_2 _Host_i2 _rep_i2 _value_i2 h_3 h_1
  let _object_i3 := (Litex.div _value_i1 _value_i2 (M.real_subset_complex _ h_2) (M.real_subset_complex _ h_3) h_1)
  have h_86 : Litex.In _object_i3 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := (Litex.div _value_i1 _value_i2 (M.real_subset_complex _ h_2) (M.real_subset_complex _ h_3) h_1)
            exact (Litex.divInR _value_i1 _value_i2 h_2 h_3 (_atomic_wd_1_0).wd.2.2))
        )
    )
  have h_87 : Litex.Same _object_i3 _object_i3 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.sameRefl (Litex.div _value_i1 _value_i2 (M.real_subset_complex _ h_2) (M.real_subset_complex _ h_3) h_1))
        )
    )
  exact h_87

noncomputable def _object_w4 := ((_template_i3 (M := M)) (Litex.number (M := M) (6 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))

theorem h_92 : (by
  let _equal_wd_1_0 := (_object_w4 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w4 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from (show (Litex.denote _equal_wd_1_0) = (M.number (3 : ℂ)) from (let _equal_wd_2_0 := (Litex.div (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) ((6 : ℂ) / (2 : ℂ)) (3 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2.1 (_equal_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num)))))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_template_x5f_guarded_x5f_quotient_x2f_statement_x2e_lit
