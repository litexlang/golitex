import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_cosine_x5f_nonzero_x5f_under_x5f_zero_x5f_subtraction_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_5 : Litex.In _value_i1 (Litex.R (M := M))) (h_1 : (by
  let _atomic_wd_1_1 := (Litex.cos _value_i1 h_5)
  exact ¬ Litex.Same (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1)), ¬ Litex.Same (Litex.number (M := M) (0 : ℂ)) (let _wd_1_0 := (Litex.sub (Litex.number (M := M) (0 : ℂ)) _value_i1 (Litex.numberInC (M := M) (0 : ℂ)) (M.real_subset_complex _ h_5));
(Litex.cos _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.subInR (Litex.number (M := M) (0 : ℂ)) _value_i1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) h_5)))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_5 h_1
          have h_50 : Litex.In _value_i1 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_5
                )
            )
          let _object_w7 := (let _wd_1_0 := (Litex.sub (Litex.number (M := M) (0 : ℂ)) _value_i1 (Litex.numberInC (M := M) (0 : ℂ)) (M.real_subset_complex _ h_50));
          (Litex.cos _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.subInR (Litex.number (M := M) (0 : ℂ)) _value_i1 (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)) h_50))))

          have h_4 : (by
            let _atomic_wd_1_1 := _object_w7
            exact ¬ Litex.Same (Litex.number (M := M) (0 : ℂ)) _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w7
                    exact (let _target := _atomic_wd_1_1; let _source := (Litex.cos _value_i1 h_50); fun _litex_equal => (Litex.cosNonzeroOfNegatedArg _target _source ((congrArg (fun v => M.subValue v (Litex.denote _source.val.arg)) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ))))).trans (Litex.zeroSubValue _source.val.arg (Litex.realToComplex _source.val.arg _source.wd))) (fun _known_equal => h_1 (_known_equal.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))).symm).symm)) ((_litex_equal.symm).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))))))
                )
            )
          exact (by
            let _atomic_wd_1_1 := _object_w7
            exact h_4)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_cosine_x5f_nonzero_x5f_under_x5f_zero_x5f_subtraction_x2f_statement_x2e_lit
