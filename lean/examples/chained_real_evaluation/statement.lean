import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_chained_x5f_real_x5f_evaluation_x2f_statement_x2e_lit

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

noncomputable def _object_i2 := (Litex.add (_object_i1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ (h_3 (M := M))) (Litex.numberInC (M := M) (1 : ℂ)))
theorem h_43 : Litex.In (_object_i2 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (Litex.add (_object_i1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ (h_3 (M := M))) (Litex.numberInC (M := M) (1 : ℂ)))
          exact (Litex.addInR (_object_i1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (h_3 (M := M)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))))
      )
  )
theorem h_44 : Litex.Same (_object_i2 (M := M)) (_object_i2 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.add (_object_i1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ (h_3 (M := M))) (Litex.numberInC (M := M) (1 : ℂ))))
      )
  )

theorem h_45 : (by
  let _chain_wd_45_1 := (_object_i2 (M := M))
  let _chain_wd_45_2 := (_object_i2 (M := M))
  exact ((by
    let _equal_wd_1_1 := _chain_wd_45_1
    exact Litex.Same (_object_i2 (M := M)) _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _chain_wd_45_2
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))))) :=
  (by
    litex_complete =>
      exact (
        (by
          let _chain_wd_45_1 := (_object_i2 (M := M))
          let _chain_wd_45_2 := (_object_i2 (M := M))
          exact (And.intro (h_44 (M := M)) (((congrArg₂ M.addValue (h_4 (M := M)) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))))).trans (((let _equal_wd_2_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) ((2 : ℂ) + (1 : ℂ)) (3 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num))))).trans ((Litex.sameRefl (Litex.number (M := M) (3 : ℂ)))).symm))))
      )
  )

theorem h_85 : Litex.Same (_object_i2 (M := M)) (_object_i2 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (And.left (h_45 (M := M)))
      )
  )

theorem h_86 : Litex.Same (_object_i2 (M := M)) (Litex.number (M := M) (3 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (And.right (h_45 (M := M)))
      )
  )

theorem h_87 : Litex.Same (_object_i2 (M := M)) (_object_i2 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (h_85 (M := M))
      )
  )

theorem h_88 : Litex.Same (_object_i2 (M := M)) (Litex.number (M := M) (3 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (h_86 (M := M))
      )
  )

theorem h_89 : Litex.Same (_object_i2 (M := M)) (Litex.number (M := M) (3 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Eq.trans (h_85 (M := M)) (h_86 (M := M)))
      )
  )

noncomputable def _object_w6 := (Litex.powNatReal (_object_i2 (M := M)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (h_43 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))

theorem h_90 : (by
  let _equal_wd_1_0 := (_object_w6 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (9 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (((congrArg₂ M.powValue (h_89 (M := M)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))))).trans (((let _equal_wd_2_0 := (Litex.powNatReal (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inOfSame (_object_i2 (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_89 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_43 (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
        (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (9 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (9 : ℂ)) ((3 : ℂ) ^ (2 : ℕ)) (9 : ℂ) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.inOfSame (_object_i2 (M := M)) (Litex.number (M := M) (3 : ℂ)) (Litex.R (M := M)) (Litex.R (M := M)) (h_89 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (h_43 (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ)) (by norm_num))))).trans ((Litex.sameRefl (Litex.number (M := M) (9 : ℂ)))).symm))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_chained_x5f_real_x5f_evaluation_x2f_statement_x2e_lit
