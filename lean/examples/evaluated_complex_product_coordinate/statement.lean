import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_complex_x5f_product_x5f_coordinate_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

theorem h_38 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (Litex.number (M := M) (1 : ℂ));
  let _wd_3_1 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) Complex.I));
  (Litex.add _wd_3_0 _wd_3_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
    let _atomic_wd_1_0 := _wd_3_1
    exact (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
  let _wd_2_1 := (Litex.sub (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) Complex.I));
  (Litex.mul _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.addInC (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2)) (by
    let _atomic_wd_1_0 := _wd_2_1
    exact (Litex.subInC (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
  (Litex.re _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.mulInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (Litex.number (M := M) (1 : ℂ));
        let _wd_3_1 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) Complex.I));
        (Litex.add _wd_3_0 _wd_3_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
          let _atomic_wd_1_0 := _wd_3_1
          exact (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
        let _wd_2_1 := (Litex.sub (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) Complex.I));
        (Litex.mul _wd_2_0 _wd_2_1 (by
          let _atomic_wd_1_0 := _wd_2_0
          exact (Litex.addInC (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2)) (by
          let _atomic_wd_1_0 := _wd_2_1
          exact (Litex.subInC (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
        (Litex.re _wd_1_0 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.mulInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = ((Litex.complexUnaryValue (M := M) (fun z : ℂ => (z.re : ℂ))) (M.mulValue (M.addValue (M.number (1 : ℂ)) (M.mulValue (M.number (2 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I)))) (M.subValue (M.number (3 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))) from rfl) (((Eq.refl ((Litex.complexUnaryValue (M := M) (fun z : ℂ => (z.re : ℂ))) (M.mulValue (M.addValue (M.number (1 : ℂ)) (M.mulValue (M.number (2 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I)))) (M.subValue (M.number (3 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))))).trans (show ((Litex.complexUnaryValue (M := M) (fun z : ℂ => (z.re : ℂ))) (M.mulValue (M.addValue (M.number (1 : ℂ)) (M.mulValue (M.number (2 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I)))) (M.subValue (M.number (3 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))) = M.number (5 : ℂ) from ((show Litex.denote (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (Litex.number (M := M) (1 : ℂ));
        let _wd_3_1 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) Complex.I));
        (Litex.add _wd_3_0 _wd_3_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
          let _atomic_wd_1_0 := _wd_3_1
          exact (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
        let _wd_2_1 := (Litex.sub (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) Complex.I));
        (Litex.mul _wd_2_0 _wd_2_1 (by
          let _atomic_wd_1_0 := _wd_2_0
          exact (Litex.addInC (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2)) (by
          let _atomic_wd_1_0 := _wd_2_1
          exact (Litex.subInC (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
        (Litex.re _wd_1_0 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.mulInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2)))) = ((Litex.complexUnaryValue (M := M) (fun z : ℂ => (z.re : ℂ))) (M.mulValue (M.addValue (M.number (1 : ℂ)) (M.mulValue (M.number (2 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I)))) (M.subValue (M.number (3 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))) from rfl)).symm.trans (((((let _complex := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (Litex.number (M := M) (1 : ℂ));
        let _wd_3_1 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) Complex.I));
        (Litex.add _wd_3_0 _wd_3_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
          let _atomic_wd_1_0 := _wd_3_1
          exact (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
        let _wd_2_1 := (Litex.sub (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) Complex.I));
        (Litex.mul _wd_2_0 _wd_2_1 (by
          let _atomic_wd_1_0 := _wd_2_0
          exact (Litex.addInC (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2)) (by
          let _atomic_wd_1_0 := _wd_2_1
          exact (Litex.subInC (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
        (Litex.re _wd_1_0 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.mulInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2)))); Litex.denoteRealPart _complex (((1 : ℂ) + ((2 : ℂ) * Complex.I)) * ((3 : ℂ) - Complex.I)) (Litex.NativeBridge.denoteMul (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
        let _wd_1_1 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) Complex.I));
        (Litex.add _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
          let _atomic_wd_1_0 := _wd_1_1
          exact (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2)))) (Litex.sub (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) Complex.I)) (by
          let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
          let _wd_1_1 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) Complex.I));
          (Litex.add _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
            let _atomic_wd_2_0 := _wd_1_1
            exact (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2))))
          exact (Litex.addInC (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2)) (by
          let _atomic_wd_1_0 := (Litex.sub (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) Complex.I))
          exact (Litex.subInC (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2)) _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) Complex.I)) (Litex.numberInC (M := M) (1 : ℂ)) (by
          let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) Complex.I))
          exact (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) Complex.I) _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) Complex.I))) (Litex.NativeBridge.denoteSub (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) Complex.I) _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) Complex.I))))).trans (congrArg M.number (by norm_num [Complex.div_re, Complex.div_im, Complex.normSq] : (((((1 : ℂ) + ((2 : ℂ) * Complex.I)) * ((3 : ℂ) - Complex.I))).re : ℂ) = (5 : ℂ))))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (5 : ℂ)))))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = (5 : ℂ)))).symm)))
      )
  )

theorem h_76 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (Litex.number (M := M) (1 : ℂ));
  let _wd_3_1 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) Complex.I));
  (Litex.add _wd_3_0 _wd_3_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
    let _atomic_wd_1_0 := _wd_3_1
    exact (Litex.mulInC (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
  let _wd_2_1 := (Litex.sub (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.numberInC (M := M) Complex.I));
  (Litex.mul _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.addInC (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2)) (by
    let _atomic_wd_1_0 := _wd_2_1
    exact (Litex.subInC (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
  (Litex.re _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.mulInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (5 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_38 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_complex_x5f_product_x5f_coordinate_x2f_statement_x2e_lit
