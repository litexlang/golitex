import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_hyperbolic_x5f_zero_x5f_values_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

noncomputable def _object_w1 := (Litex.sinh (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))

theorem h_1 : (by
  let _equal_wd_1_0 := (_object_w1 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w1 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (Real.sinh ((0 : ℂ)).re : ℂ) (0 : ℂ) (let _hyp := _equal_wd_1_0; Litex.denoteSinh _hyp ((0 : ℂ)).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (0 : ℂ) _hyp.wd (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
      )
  )

noncomputable def _object_w3 := (Litex.cosh (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))

theorem h_4 : (by
  let _equal_wd_1_0 := (_object_w3 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w3 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (Real.cosh ((0 : ℂ)).re : ℂ) (1 : ℂ) (let _hyp := _equal_wd_1_0; Litex.denoteCosh _hyp ((0 : ℂ)).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (0 : ℂ) _hyp.wd (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))
      )
  )

noncomputable def _object_w5 := (Litex.tanh (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))

theorem h_7 : (by
  let _equal_wd_1_0 := (_object_w5 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w5 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (Real.tanh ((0 : ℂ)).re : ℂ) (0 : ℂ) (let _hyp := _equal_wd_1_0; Litex.denoteTanh _hyp ((0 : ℂ)).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (0 : ℂ) _hyp.wd (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
      )
  )

noncomputable def _object_w6 := (Litex.sech (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num)))

theorem h_10 : (by
  let _equal_wd_1_0 := (_object_w6 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w6 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (Litex.nativeSech ((0 : ℂ)).re : ℂ) (1 : ℂ) (let _hyp := _equal_wd_1_0; Litex.denoteSech _hyp ((0 : ℂ)).re (Litex.NativeBridge.denoteRealOfDenoteNumber _hyp.val.arg (0 : ℂ) _hyp.wd (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_hyperbolic_x5f_zero_x5f_values_x2f_statement_x2e_lit
