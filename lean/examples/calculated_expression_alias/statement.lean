import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_calculated_x5f_expression_x5f_alias_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

noncomputable def _object_i1 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))
theorem h_3 : Litex.Same (_object_i1 (M := M)) (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) :=
  (Litex.sameRefl (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))))

theorem h_4 : Litex.Same (_object_i1 (M := M)) (Litex.number (M := M) (5 : ℂ)) :=
  (((h_3 (M := M))).trans (((Litex.NativeBridge.sameOfDenoteNumber (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ))) (Litex.number (M := M) (5 : ℂ)) ((2 : ℂ) + (3 : ℂ)) (5 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (by norm_num))).trans (show @Eq M.Value _ _ from Eq.refl _)))

theorem h_15 : Litex.Same (Litex.number (M := M) (5 : ℂ)) (_object_i1 (M := M)) :=
  ((h_4 (M := M))).symm
end LitexCompiled.file_lean_x2f_examples_x2f_calculated_x5f_expression_x5f_alias_x2f_statement_x2e_lit
