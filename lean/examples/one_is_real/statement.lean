import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_one_x5f_is_x5f_real_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

theorem h_1 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_one_x5f_is_x5f_real_x2f_statement_x2e_lit
