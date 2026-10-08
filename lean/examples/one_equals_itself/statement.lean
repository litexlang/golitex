import Litex

namespace LitexCompiled.file_lean_x2f_examples_x2f_one_x5f_equals_x5f_itself_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

theorem fact_1 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
  (Litex.sameRefl (Litex.number (M := M) (1 : ℂ)))
end LitexCompiled.file_lean_x2f_examples_x2f_one_x5f_equals_x5f_itself_x2f_statement_x2e_lit
