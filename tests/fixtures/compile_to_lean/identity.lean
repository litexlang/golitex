import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_tests_x2f_fixtures_x2f_compile_x5f_to_x5f_lean_x2f_identity_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

theorem h_1 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (show @Eq M.Value _ _ from Eq.refl _)
      )
  )
end LitexCompiled.file_tests_x2f_fixtures_x2f_compile_x5f_to_x5f_lean_x2f_identity_x2e_lit
