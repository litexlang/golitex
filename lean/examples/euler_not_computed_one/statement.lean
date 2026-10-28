import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_euler_x5f_not_x5f_computed_x5f_one_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

noncomputable def _object_w1 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (0 : ℂ)))

theorem h_1 : (by
  let _atomic_wd_1_0 := (_object_w1 (M := M))
  exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) ((Real.exp 1 : ℝ) : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w1 (M := M))
          exact (fun _litex_equal => (Litex.eulerNonunit (M := M)) ((_litex_equal.symm).trans (((Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) + (0 : ℂ)) = (1 : ℂ)))))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_euler_x5f_not_x5f_computed_x5f_one_x2f_statement_x2e_lit
