import Litex

namespace LitexCompiled.file_lean_x2f_examples_x2f_defined_x5f_real_x5f_value_x5f_alias_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

noncomputable def _object_i1 := (Litex.number (M := M) (2 : ℂ))

noncomputable def _object_i2 := (_object_i1 (M := M))

theorem fact_3 : Litex.Same (_object_i2 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (((((Litex.sameRefl (_object_i2 (M := M)))).trans (Litex.sameRefl (_object_i1 (M := M))))).trans (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))))

theorem fact_4 : Litex.In (_object_i2 (M := M)) (Litex.R (M := M)) :=
  (Litex.inOfSame (_object_i1 (M := M)) (_object_i2 (M := M)) (Litex.R (M := M)) (Litex.R (M := M)) (((Litex.sameRefl (_object_i1 (M := M)))).trans ((Litex.sameRefl (_object_i1 (M := M)))).symm) (Litex.sameRefl (Litex.R (M := M))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.R (M := M)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num))))
end LitexCompiled.file_lean_x2f_examples_x2f_defined_x5f_real_x5f_value_x5f_alias_x2f_statement_x2e_lit
