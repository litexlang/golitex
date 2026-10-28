import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_euler_x5f_not_x5f_one_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_1 : ¬ Litex.Same (Litex.number (M := M) ((Real.exp 1 : ℝ) : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (fun _litex_equal => (Litex.eulerNonunit (M := M)) ((_litex_equal).trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ))))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_euler_x5f_not_x5f_one_x2f_statement_x2e_lit
