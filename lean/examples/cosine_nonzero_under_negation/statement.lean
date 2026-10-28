import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_cosine_x5f_nonzero_x5f_under_x5f_negation_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_5 : Litex.In _value_i1 (Litex.R (M := M))) (h_1 : (by
  let _atomic_wd_1_0 := (Litex.cos _value_i1 h_5)
  exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))), ¬ Litex.Same (let _wd_1_0 := (Litex.neg _value_i1 (M.real_subset_complex _ h_5));
(Litex.cos _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.negInR _value_i1 h_5)))) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_5 h_1
          have h_41 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_5
                )
            )
          let _object_w7 := (let _wd_1_0 := (Litex.neg _value_i1 (M.real_subset_complex _ h_41));
          (Litex.cos _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.negInR _value_i1 h_41))))

          have h_4 : (by
            let _atomic_wd_1_0 := _object_w7
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w7
                    exact (let _target := _atomic_wd_1_0; let _source := (Litex.cos _value_i1 h_41); fun _litex_equal => (Litex.cosNonzeroOfNegatedArg _target _source rfl (fun _known_equal => h_1 (_known_equal.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))).symm))) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          exact (by
            let _atomic_wd_1_0 := _object_w7
            exact h_4)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_cosine_x5f_nonzero_x5f_under_x5f_negation_x2f_statement_x2e_lit
