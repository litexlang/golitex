import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_numeric_x5f_citations_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

noncomputable def _object_i1 := (Litex.number (M := M) (10 : ℂ))
theorem h_3 : Litex.In (_object_i1 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.NativeBridge.numberInROfEq (M := M) (10 : ℂ) (10 : ℝ) (by norm_num))
      )
  )
theorem h_4 : Litex.Same (_object_i1 (M := M)) (Litex.number (M := M) (10 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.number (M := M) (10 : ℂ)))
      )
  )

theorem h_18 : (by
  let _equal_wd_1_0 := (Litex.add (_object_i1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ (h_3 (M := M))) (Litex.numberInC (M := M) (1 : ℂ)))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (11 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (Litex.add (_object_i1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ (h_3 (M := M))) (Litex.numberInC (M := M) (1 : ℂ)));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (11 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (11 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (M.addValue (Litex.denote (_object_i1 (M := M))) (M.number (1 : ℂ))) from congrArg₂ M.addValue (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl) (show Litex.denote (Litex.number (M := M) (1 : ℂ)) = (M.number (1 : ℂ)) from rfl)) (((congrArg₂ M.addValue (Eq.trans (Eq.trans (Eq.symm (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl)) (h_4 (M := M))) (show Litex.denote (Litex.number (M := M) (10 : ℂ)) = (M.number (10 : ℂ)) from rfl)) (Eq.refl (M.number (1 : ℂ))))).trans (show (M.addValue (M.number (10 : ℂ)) (M.number (1 : ℂ))) = M.number (11 : ℂ) from ((congrArg₂ M.addValue (show (M.number (10 : ℂ)) = M.number (10 : ℂ) from (congrArg M.number (show (10 : ℂ) = (10 : ℂ) from by norm_num))) (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num)))).trans ((M.add_numbers (10 : ℂ) (1 : ℂ)).trans (congrArg M.number (by norm_num)))))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (11 : ℂ))).trans (congrArg M.number (by norm_num : (11 : ℂ) = (11 : ℂ)))).symm)))
      )
  )

theorem h_32 : (by
  let _equal_wd_1_0 := (Litex.add (_object_i1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ (h_3 (M := M))) (Litex.numberInC (M := M) (1 : ℂ)))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (11 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_18 (M := M))
      )
  )

noncomputable def _object_i2 := (Litex.number (M := M) (4 : ℂ))
theorem h_38 : Litex.In (_object_i2 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.NativeBridge.numberInROfEq (M := M) (4 : ℂ) (4 : ℝ) (by norm_num))
      )
  )
theorem h_39 : Litex.Same (_object_i2 (M := M)) (Litex.number (M := M) (4 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.number (M := M) (4 : ℂ)))
      )
  )

theorem h_131 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.mul (_object_i1 (M := M)) (_object_i2 (M := M)) (M.real_subset_complex _ (h_3 (M := M))) (M.real_subset_complex _ (h_38 (M := M))));
  let _wd_1_1 := (_object_i2 (M := M));
  (Litex.sub _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.mulInC (_object_i1 (M := M)) _wd_1_1 (M.real_subset_complex _ (h_3 (M := M))) (M.real_subset_complex _ (h_38 (M := M))))) (M.real_subset_complex _ (h_38 (M := M)))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (36 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.mul (_object_i1 (M := M)) (_object_i2 (M := M)) (M.real_subset_complex _ (h_3 (M := M))) (M.real_subset_complex _ (h_38 (M := M))));
        let _wd_1_1 := (_object_i2 (M := M));
        (Litex.sub _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.mulInC (_object_i1 (M := M)) _wd_1_1 (M.real_subset_complex _ (h_3 (M := M))) (M.real_subset_complex _ (h_38 (M := M))))) (M.real_subset_complex _ (h_38 (M := M)))));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (36 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (36 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (M.subValue (M.mulValue (Litex.denote (_object_i1 (M := M))) (Litex.denote (_object_i2 (M := M)))) (Litex.denote (_object_i2 (M := M)))) from congrArg₂ M.subValue (show Litex.denote (_equal_wd_1_0).val.left = (M.mulValue (Litex.denote (_object_i1 (M := M))) (Litex.denote (_object_i2 (M := M)))) from congrArg₂ M.mulValue (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl) (show Litex.denote (_object_i2 (M := M)) = (Litex.denote (_object_i2 (M := M))) from rfl)) (show Litex.denote (_object_i2 (M := M)) = (Litex.denote (_object_i2 (M := M))) from rfl)) (((congrArg₂ M.subValue (congrArg₂ M.mulValue (Eq.trans (Eq.trans (Eq.symm (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl)) (h_4 (M := M))) (show Litex.denote (Litex.number (M := M) (10 : ℂ)) = (M.number (10 : ℂ)) from rfl)) (Eq.trans (Eq.trans (Eq.symm (show Litex.denote (_object_i2 (M := M)) = (Litex.denote (_object_i2 (M := M))) from rfl)) (h_39 (M := M))) (show Litex.denote (Litex.number (M := M) (4 : ℂ)) = (M.number (4 : ℂ)) from rfl))) (Eq.trans (Eq.trans (Eq.symm (show Litex.denote (_object_i2 (M := M)) = (Litex.denote (_object_i2 (M := M))) from rfl)) (h_39 (M := M))) (show Litex.denote (Litex.number (M := M) (4 : ℂ)) = (M.number (4 : ℂ)) from rfl)))).trans (show (M.subValue (M.mulValue (M.number (10 : ℂ)) (M.number (4 : ℂ))) (M.number (4 : ℂ))) = M.number (36 : ℂ) from ((congrArg₂ M.subValue (show (M.mulValue (M.number (10 : ℂ)) (M.number (4 : ℂ))) = M.number (40 : ℂ) from ((congrArg₂ M.mulValue (show (M.number (10 : ℂ)) = M.number (10 : ℂ) from (congrArg M.number (show (10 : ℂ) = (10 : ℂ) from by norm_num))) (show (M.number (4 : ℂ)) = M.number (4 : ℂ) from (congrArg M.number (show (4 : ℂ) = (4 : ℂ) from by norm_num)))).trans ((M.mul_numbers (10 : ℂ) (4 : ℂ)).trans (congrArg M.number (by norm_num))))) (show (M.number (4 : ℂ)) = M.number (4 : ℂ) from (congrArg M.number (show (4 : ℂ) = (4 : ℂ) from by norm_num)))).trans ((M.sub_numbers (40 : ℂ) (4 : ℂ)).trans (congrArg M.number (by norm_num)))))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (36 : ℂ))).trans (congrArg M.number (by norm_num : (36 : ℂ) = (36 : ℂ)))).symm)))
      )
  )

theorem h_223 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.mul (_object_i1 (M := M)) (_object_i2 (M := M)) (M.real_subset_complex _ (h_3 (M := M))) (M.real_subset_complex _ (h_38 (M := M))));
  let _wd_1_1 := (_object_i2 (M := M));
  (Litex.sub _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.mulInC (_object_i1 (M := M)) _wd_1_1 (M.real_subset_complex _ (h_3 (M := M))) (M.real_subset_complex _ (h_38 (M := M))))) (M.real_subset_complex _ (h_38 (M := M)))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (36 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_131 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_numeric_x5f_citations_x2f_statement_x2e_lit
