import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_tests_x2f_fixtures_x2f_compile_x5f_to_x5f_lean_x2f_resolved_x5f_positive_x5f_bound_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_16 : Litex.In _value_i1 (Litex.R (M := M))) (h_1 : Litex.Le (Litex.number (M := M) (1 : ℂ)) _value_i1), Litex.In _value_i1 (Litex.RPos (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_16 h_1
          have h_2 : Litex.In _value_i1 (Litex.RPos (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_intro _value_i1 h_16 (by
                    have _sign_real := h_16
                    exact (Litex.ltLeTrans (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) _value_i1 (Litex.NativeBridge.ltOfDenoteReal (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (1 : ℂ)) 0 (1 : ℝ) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num))) (by norm_num)) h_1)
                  ))
                )
            )
          have h_66 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRPos_positive _value_i1 h_2)
                )
            )
          have h_67 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i1 h_66)
                )
            )
          have h_68 : ¬ Litex.Same _value_i1 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i1 h_66) _litex_zero.symm)
                )
            )
          exact h_2
        )
      )
  )
end LitexCompiled.file_tests_x2f_fixtures_x2f_compile_x5f_to_x5f_lean_x2f_resolved_x5f_positive_x5f_bound_x2e_lit
