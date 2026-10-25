import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_complex_x5f_observation_x5f_values_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

noncomputable def _object_w1 := (Litex.re (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) Complex.I))

theorem h_1 : (by
  let _equal_wd_1_0 := (_object_w1 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w1 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (0 : ℂ) (0 : ℂ) (((let _complex := _equal_wd_1_0; Litex.denoteRealPart _complex Complex.I (Litex.NativeBridge.denoteNumber (M := M) Complex.I))).trans (congrArg M.number (by norm_num : ((Complex.I).re : ℂ) = (0 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
      )
  )

noncomputable def _object_w3 := (Litex.img (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) Complex.I))

theorem h_4 : (by
  let _equal_wd_1_0 := (_object_w3 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w3 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (1 : ℂ) (((let _complex := _equal_wd_1_0; Litex.denoteImaginaryPart _complex Complex.I (Litex.NativeBridge.denoteNumber (M := M) Complex.I))).trans (congrArg M.number (by norm_num : ((Complex.I).im : ℂ) = (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))
      )
  )

noncomputable def _object_w5 := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (3 : ℂ));
let _wd_2_1 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) Complex.I));
(Litex.add _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (3 : ℂ)) (by
  let _atomic_wd_1_0 := _wd_2_1
  exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
(Litex.conj _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))))

noncomputable def _object_w6 := (let _wd_1_0 := (Litex.number (M := M) (3 : ℂ));
let _wd_1_1 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) Complex.I));
(Litex.sub _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (3 : ℂ)) (by
  let _atomic_wd_1_0 := _wd_1_1
  exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))))

theorem h_7 : (by
  let _equal_wd_1_0 := (_object_w5 (M := M))
  let _equal_wd_1_1 := (_object_w6 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w5 (M := M));
        let _equal_wd_1_1 := (_object_w6 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (star (((3 : ℂ) + ((4 : ℂ) * Complex.I)))) ((3 : ℂ) - ((4 : ℂ) * Complex.I)) (let _complex := _equal_wd_1_0; Litex.denoteConjugate _complex ((3 : ℂ) + ((4 : ℂ) * Complex.I)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (3 : ℂ)) ((_equal_wd_1_0).val.arg).val.right ((_equal_wd_1_0).val.arg).wd.1 ((_equal_wd_1_0).val.arg).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (((_equal_wd_1_0).val.arg).val.right).wd.1 (((_equal_wd_1_0).val.arg).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) Complex.I)))) (Litex.NativeBridge.denoteSub (Litex.number (M := M) (3 : ℂ)) (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) ((_equal_wd_1_1).val.right).wd.1 ((_equal_wd_1_1).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) Complex.I))) (by norm_num [Complex.ext_iff]))))
      )
  )

noncomputable def _object_w7 := (let _wd_1_0 := ((_object_w5 (M := M))).val.arg;
(Litex.complexAbs _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))))

theorem h_28 : (by
  let _equal_wd_1_0 := (_object_w7 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w7 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ)) (5 : ℂ) (5 : ℂ) (((let _complex := _equal_wd_1_0; Litex.denoteComplexAbs _complex ((3 : ℂ) + ((4 : ℂ) * Complex.I)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (3 : ℂ)) ((_equal_wd_1_0).val.arg).val.right ((_equal_wd_1_0).val.arg).wd.1 ((_equal_wd_1_0).val.arg).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (((_equal_wd_1_0).val.arg).val.right).wd.1 (((_equal_wd_1_0).val.arg).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) Complex.I))))).trans (congrArg M.number (by have _norm : ‖(((3 : ℂ) + ((4 : ℂ) * Complex.I)))‖ = (5 : ℝ) := (by rw [Complex.norm_def]; exact (Real.sqrt_eq_iff_eq_sq (Complex.normSq_nonneg _) (by norm_num)).mpr (by norm_num [Complex.normSq])); exact (congrArg (fun r : ℝ => (r : ℂ)) _norm).trans (by norm_num) : (‖(((3 : ℂ) + ((4 : ℂ) * Complex.I)))‖ : ℂ) = (5 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (by norm_num))))
      )
  )

noncomputable def _object_w9 := (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (5 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
let _wd_2_1 := (let _wd_3_0 := (Litex.div (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (5 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
let _wd_3_1 := (Litex.number (M := M) Complex.I);
(Litex.mul _wd_3_0 _wd_3_1 (by
  let _atomic_wd_1_0 := _wd_3_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((4 : ℂ) / (5 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)))).trans (congrArg M.number (by norm_num : ((4 : ℂ) / (5 : ℂ)) = ((4 : ℂ) / (5 : ℂ))))) (Litex.numberInC (M := M) ((4 : ℂ) / (5 : ℂ))))) (Litex.numberInC (M := M) Complex.I)));
(Litex.add _wd_2_0 _wd_2_1 (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((3 : ℂ) / (5 : ℂ)) (Litex.C (M := M)) (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)))).trans (congrArg M.number (by norm_num : ((3 : ℂ) / (5 : ℂ)) = ((3 : ℂ) / (5 : ℂ))))) (Litex.numberInC (M := M) ((3 : ℂ) / (5 : ℂ))))) (by
  let _atomic_wd_1_0 := _wd_2_1
  exact (Litex.mulInC (_atomic_wd_1_0).val.left (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
(Litex.complexAbs _wd_1_0 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.addInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))))

theorem h_43 : (by
  let _equal_wd_1_0 := (_object_w9 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w9 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (1 : ℂ) (1 : ℂ) (((let _complex := _equal_wd_1_0; Litex.denoteComplexAbs _complex (((3 : ℂ) / (5 : ℂ)) + (((4 : ℂ) / (5 : ℂ)) * Complex.I)) (Litex.NativeBridge.denoteAdd ((_equal_wd_1_0).val.arg).val.left ((_equal_wd_1_0).val.arg).val.right ((_equal_wd_1_0).val.arg).wd.1 ((_equal_wd_1_0).val.arg).wd.2 _ _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (5 : ℂ)) (((_equal_wd_1_0).val.arg).val.left).wd.1 (((_equal_wd_1_0).val.arg).val.left).wd.2.1 (((_equal_wd_1_0).val.arg).val.left).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))) (Litex.NativeBridge.denoteMul (((_equal_wd_1_0).val.arg).val.right).val.left (Litex.number (M := M) Complex.I) (((_equal_wd_1_0).val.arg).val.right).wd.1 (((_equal_wd_1_0).val.arg).val.right).wd.2 _ _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) (5 : ℂ)) ((((_equal_wd_1_0).val.arg).val.right).val.left).wd.1 ((((_equal_wd_1_0).val.arg).val.right).val.left).wd.2.1 ((((_equal_wd_1_0).val.arg).val.right).val.left).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) Complex.I))))).trans (congrArg M.number (by have _norm : ‖((((3 : ℂ) / (5 : ℂ)) + (((4 : ℂ) / (5 : ℂ)) * Complex.I)))‖ = (1 : ℝ) := (by rw [Complex.norm_def]; exact (Real.sqrt_eq_iff_eq_sq (Complex.normSq_nonneg _) (by norm_num)).mpr (by norm_num [Complex.normSq])); exact (congrArg (fun r : ℝ => (r : ℂ)) _norm).trans (by norm_num) : (‖((((3 : ℂ) / (5 : ℂ)) + (((4 : ℂ) / (5 : ℂ)) * Complex.I)))‖ : ℂ) = (1 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_complex_x5f_observation_x5f_values_x2f_statement_x2e_lit
