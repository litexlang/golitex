import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_complex_x5f_modulus_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

theorem h_14 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (3 : ℂ));
  let _wd_2_1 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) Complex.I));
  (Litex.add _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (3 : ℂ)) (by
    let _atomic_wd_1_0 := _wd_2_1
    exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
  (Litex.complexAbs _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (3 : ℂ));
        let _wd_2_1 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) Complex.I));
        (Litex.add _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (3 : ℂ)) (by
          let _atomic_wd_1_0 := _wd_2_1
          exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
        (Litex.complexAbs _wd_1_0 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = ((Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))) from rfl) (((Eq.refl ((Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))))).trans (show ((Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))) = M.number (5 : ℂ) from ((show Litex.denote (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (3 : ℂ));
        let _wd_2_1 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) Complex.I));
        (Litex.add _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (3 : ℂ)) (by
          let _atomic_wd_1_0 := _wd_2_1
          exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
        (Litex.complexAbs _wd_1_0 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2)))) = ((Litex.complexUnaryValue (M := M) (fun z : ℂ => (‖z‖ : ℂ))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))) from rfl)).symm.trans (((((let _complex := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (3 : ℂ));
        let _wd_2_1 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) Complex.I));
        (Litex.add _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (3 : ℂ)) (by
          let _atomic_wd_1_0 := _wd_2_1
          exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
        (Litex.complexAbs _wd_1_0 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2)))); Litex.denoteComplexAbs _complex ((3 : ℂ) + ((4 : ℂ) * Complex.I)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (3 : ℂ)) (Litex.mul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) Complex.I)) (Litex.numberInC (M := M) (3 : ℂ)) (by
          let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) Complex.I))
          exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) Complex.I) _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) Complex.I))))).trans (congrArg M.number (by have _norm : ‖(((3 : ℂ) + ((4 : ℂ) * Complex.I)))‖ = (5 : ℝ) := (by rw [Complex.norm_def]; exact (Real.sqrt_eq_iff_eq_sq (Complex.normSq_nonneg _) (by norm_num)).mpr (by norm_num [Complex.normSq])); exact (congrArg (fun r : ℝ => (r : ℂ)) _norm).trans (by norm_num) : (‖(((3 : ℂ) + ((4 : ℂ) * Complex.I)))‖ : ℂ) = (5 : ℂ))))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (5 : ℂ)))))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (5 : ℂ)))).symm)))
      )
  )

theorem h_28 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (3 : ℂ));
  let _wd_2_1 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) Complex.I));
  (Litex.add _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (3 : ℂ)) (by
    let _atomic_wd_1_0 := _wd_2_1
    exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
  (Litex.complexAbs _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_14 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_complex_x5f_modulus_x2f_statement_x2e_lit
