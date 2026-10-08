import Litex

namespace LitexCompiled.file_lean_x2f_examples_x2f_one_x5f_is_x5f_real_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

theorem fact_1 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) :=
  (Litex.NativeBridge.numberInR (M := M) (1 : ℝ))
end LitexCompiled.file_lean_x2f_examples_x2f_one_x5f_is_x5f_real_x2f_statement_x2e_lit
