import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_chained_x5f_real_x5f_evaluation_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

noncomputable def _object_i1 := (Litex.number (M := M) (2 : ℂ))
theorem h_3 : Litex.In (_object_i1 (M := M)) (Litex.R (M := M)) :=
  (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
theorem h_4 : Litex.Same (_object_i1 (M := M)) (Litex.number (M := M) (2 : ℂ)) :=
  (Litex.sameRefl (Litex.number (M := M) (2 : ℂ)))

noncomputable def _object_i2 := (Litex.add (_object_i1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ (h_3 (M := M))) (Litex.numberInC (M := M) (1 : ℂ)))
theorem h_43 : Litex.In (_object_i2 (M := M)) (Litex.R (M := M)) :=
  (Litex.addInR (_object_i1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (h_3 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))
theorem h_44 : Litex.Same (_object_i2 (M := M)) (Litex.add (_object_i1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ (h_3 (M := M))) (Litex.numberInC (M := M) (1 : ℂ))) :=
  (Litex.sameRefl (Litex.add (_object_i1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ (h_3 (M := M))) (Litex.numberInC (M := M) (1 : ℂ))))

theorem h_45 : (Litex.Same (_object_i2 (M := M)) (Litex.add (_object_i1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ (h_3 (M := M))) (Litex.numberInC (M := M) (1 : ℂ)))) ∧ (Litex.Same (Litex.add (_object_i1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ (h_3 (M := M))) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (3 : ℂ))) :=
  (And.intro (h_44 (M := M)) (((congrArg₂ M.addValue (h_4 (M := M)) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))))).trans (((Litex.NativeBridge.sameOfDenoteNumber (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (3 : ℂ)) ((2 : ℂ) + (1 : ℂ)) (3 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num))).trans ((Litex.sameRefl (Litex.number (M := M) (3 : ℂ)))).symm)))

theorem h_85 : Litex.Same (_object_i2 (M := M)) (Litex.add (_object_i1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ (h_3 (M := M))) (Litex.numberInC (M := M) (1 : ℂ))) :=
  (And.left (h_45 (M := M)))

theorem h_86 : Litex.Same (Litex.add (_object_i1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ (h_3 (M := M))) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (3 : ℂ)) :=
  (And.right (h_45 (M := M)))

theorem h_87 : Litex.Same (_object_i2 (M := M)) (Litex.add (_object_i1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ (h_3 (M := M))) (Litex.numberInC (M := M) (1 : ℂ))) :=
  (h_85 (M := M))

theorem h_88 : Litex.Same (Litex.add (_object_i1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ (h_3 (M := M))) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.number (M := M) (3 : ℂ)) :=
  (h_86 (M := M))

theorem h_89 : Litex.Same (_object_i2 (M := M)) (Litex.number (M := M) (3 : ℂ)) :=
  (Eq.trans (h_85 (M := M)) (h_86 (M := M)))

noncomputable def _object_w5 := (Litex.powNatReal (_object_i2 (M := M)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (h_43 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))

theorem h_90 : Litex.Same (_object_w5 (M := M)) (Litex.number (M := M) (9 : ℂ)) :=
  (((congrArg₂ M.powValue (h_89 (M := M)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))))).trans (((Litex.NativeBridge.sameOfDenoteNumber (Litex.powNatReal (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inOfSame (_object_i2 (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_89 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_43 (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.number (M := M) (9 : ℂ)) ((3 : ℂ) ^ (2 : ℕ)) (9 : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inOfSame (_object_i2 (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_89 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_43 (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ)) (by norm_num))).trans ((Litex.sameRefl (Litex.number (M := M) (9 : ℂ)))).symm))
end LitexCompiled.file_lean_x2f_examples_x2f_chained_x5f_real_x5f_evaluation_x2f_statement_x2e_lit
