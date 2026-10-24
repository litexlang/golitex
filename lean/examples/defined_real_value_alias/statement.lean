import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_defined_x5f_real_x5f_value_x5f_alias_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

noncomputable def _object_i1 := (Litex.number (M := M) (2 : ℂ))
theorem h_3 : Litex.In (_object_i1 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
      )
  )
theorem h_4 : Litex.Same (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.number (M := M) (2 : ℂ)))
      )
  )

noncomputable def _object_i2 := (_object_i1 (M := M))
theorem h_5 : Litex.Same (_object_i2 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem h_6 : Litex.Same (_object_i2 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (((h_5 (M := M))).trans (h_4 (M := M)))
      )
  )

theorem h_8 : Litex.In (_object_i2 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inOfSame (_object_i1 (M := M)) (_object_i2 (M := M)) (Litex.R (M := M)) (Litex.R (M := M)) ((h_5 (M := M))).symm (show @Eq M.Value _ _ from Eq.refl _) (h_3 (M := M)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_defined_x5f_real_x5f_value_x5f_alias_x2f_statement_x2e_lit
