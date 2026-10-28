import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_inequality_x5f_from_x5f_swapped_x5f_nonzero_x5f_sum_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_5 : Litex.In _value_i1 (Litex.C (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_6 : Litex.In _value_i2 (Litex.C (M := M))) (h_1 : (by
  let _atomic_wd_1_0 := (Litex.add _value_i2 _value_i1 h_6 h_5)
  exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))), ¬ Litex.Same _value_i1 (Litex.neg _value_i2 h_6) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_5 _Host_i2 _rep_i2 _value_i2 h_6 h_1
          have h_27 : Litex.In _value_i1 (Litex.C (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_5
                )
            )
          have h_28 : Litex.In _value_i2 (Litex.C (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_6
                )
            )
          let _object_w7 := (Litex.neg _value_i2 h_28)

          have h_4 : (by
            let _atomic_wd_1_1 := _object_w7
            exact ¬ Litex.Same _value_i1 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w7
                    exact (let _sum := (Litex.add _value_i2 _value_i1 h_28 h_27); let _other := _atomic_wd_1_1; fun _litex_equal => (Litex.notSameNegOfNonzeroSumRight _sum _other rfl (fun _known_equal => h_1 (_known_equal.trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))).symm))) _litex_equal))
                )
            )
          exact (by
            let _atomic_wd_1_1 := _object_w7
            exact h_4)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_inequality_x5f_from_x5f_swapped_x5f_nonzero_x5f_sum_x2f_statement_x2e_lit
