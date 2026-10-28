import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_complex_x5f_coordinate_x5f_arithmetic_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

theorem h_55 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (Litex.number (M := M) (3 : ℂ));
  let _wd_3_1 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) Complex.I));
  (Litex.add _wd_3_0 _wd_3_1 (Litex.numberInC (M := M) (3 : ℂ)) (by
    let _atomic_wd_1_0 := _wd_3_1
    exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
  (Litex.re _wd_2_0 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
  let _wd_1_1 := (let _wd_2_0 := (_wd_1_0).val.arg;
  (Litex.img _wd_2_0 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (_wd_1_1).val.arg;
    (Litex.re _wd_2_0 (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).val.right (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2))))
    exact (Litex.reInC _atomic_wd_1_0)) (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (_wd_1_1).val.arg;
    (Litex.img _wd_2_0 (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).val.right (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2))))
    exact (Litex.imgInC _atomic_wd_1_0))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (7 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (Litex.number (M := M) (3 : ℂ));
        let _wd_3_1 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) Complex.I));
        (Litex.add _wd_3_0 _wd_3_1 (Litex.numberInC (M := M) (3 : ℂ)) (by
          let _atomic_wd_1_0 := _wd_3_1
          exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
        (Litex.re _wd_2_0 (by
          let _atomic_wd_1_0 := _wd_2_0
          exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
        let _wd_1_1 := (let _wd_2_0 := (_wd_1_0).val.arg;
        (Litex.img _wd_2_0 (by
          let _atomic_wd_1_0 := _wd_2_0
          exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
        (Litex.add _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (_wd_1_1).val.arg;
          (Litex.re _wd_2_0 (by
            let _atomic_wd_2_0 := _wd_2_0
            exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).val.right (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2))))
          exact (Litex.reInC _atomic_wd_1_0)) (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (_wd_1_1).val.arg;
          (Litex.img _wd_2_0 (by
            let _atomic_wd_2_0 := _wd_2_0
            exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).val.right (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2))))
          exact (Litex.imgInC _atomic_wd_1_0))));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (7 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (7 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (M.addValue ((Litex.complexUnaryValue (M := M) (fun z : ℂ => (z.re : ℂ))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))) ((Litex.complexUnaryValue (M := M) (fun z : ℂ => (z.im : ℂ))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I)))))) from congrArg₂ M.addValue (show Litex.denote (_equal_wd_1_0).val.left = ((Litex.complexUnaryValue (M := M) (fun z : ℂ => (z.re : ℂ))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))) from rfl) (show Litex.denote (_equal_wd_1_0).val.right = ((Litex.complexUnaryValue (M := M) (fun z : ℂ => (z.im : ℂ))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))) from rfl)) (((Eq.refl (M.addValue ((Litex.complexUnaryValue (M := M) (fun z : ℂ => (z.re : ℂ))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))) ((Litex.complexUnaryValue (M := M) (fun z : ℂ => (z.im : ℂ))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I)))))))).trans (show (M.addValue ((Litex.complexUnaryValue (M := M) (fun z : ℂ => (z.re : ℂ))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))) ((Litex.complexUnaryValue (M := M) (fun z : ℂ => (z.im : ℂ))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I)))))) = M.number (7 : ℂ) from ((congrArg₂ M.addValue (show ((Litex.complexUnaryValue (M := M) (fun z : ℂ => (z.re : ℂ))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))) = M.number (3 : ℂ) from ((show Litex.denote (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (3 : ℂ));
        let _wd_2_1 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) Complex.I));
        (Litex.add _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (3 : ℂ)) (by
          let _atomic_wd_1_0 := _wd_2_1
          exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
        (Litex.re _wd_1_0 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2)))) = ((Litex.complexUnaryValue (M := M) (fun z : ℂ => (z.re : ℂ))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))) from rfl)).symm.trans (((((let _complex := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (3 : ℂ));
        let _wd_2_1 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) Complex.I));
        (Litex.add _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (3 : ℂ)) (by
          let _atomic_wd_1_0 := _wd_2_1
          exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
        (Litex.re _wd_1_0 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2)))); Litex.denoteRealPart _complex ((3 : ℂ) + ((4 : ℂ) * Complex.I)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (3 : ℂ)) (Litex.mul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) Complex.I)) (Litex.numberInC (M := M) (3 : ℂ)) (by
          let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) Complex.I))
          exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) Complex.I) _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) Complex.I))))).trans (congrArg M.number (by norm_num [Complex.div_re, Complex.div_im, Complex.normSq] : ((((3 : ℂ) + ((4 : ℂ) * Complex.I))).re : ℂ) = (3 : ℂ))))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ))))) (show ((Litex.complexUnaryValue (M := M) (fun z : ℂ => (z.im : ℂ))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))) = M.number (4 : ℂ) from ((show Litex.denote (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (3 : ℂ));
        let _wd_2_1 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) Complex.I));
        (Litex.add _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (3 : ℂ)) (by
          let _atomic_wd_1_0 := _wd_2_1
          exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
        (Litex.img _wd_1_0 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2)))) = ((Litex.complexUnaryValue (M := M) (fun z : ℂ => (z.im : ℂ))) (M.addValue (M.number (3 : ℂ)) (M.mulValue (M.number (4 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))))) from rfl)).symm.trans (((((let _complex := (let _wd_1_0 := (let _wd_2_0 := (Litex.number (M := M) (3 : ℂ));
        let _wd_2_1 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) Complex.I));
        (Litex.add _wd_2_0 _wd_2_1 (Litex.numberInC (M := M) (3 : ℂ)) (by
          let _atomic_wd_1_0 := _wd_2_1
          exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
        (Litex.img _wd_1_0 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2)))); Litex.denoteImaginaryPart _complex ((3 : ℂ) + ((4 : ℂ) * Complex.I)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (3 : ℂ)) (Litex.mul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) Complex.I)) (Litex.numberInC (M := M) (3 : ℂ)) (by
          let _atomic_wd_1_0 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) Complex.I))
          exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) Complex.I) _ _ (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) Complex.I))))).trans (congrArg M.number (by norm_num [Complex.div_re, Complex.div_im, Complex.normSq] : ((((3 : ℂ) + ((4 : ℂ) * Complex.I))).im : ℂ) = (4 : ℂ))))).trans (congrArg M.number (by norm_num : (4 : ℂ) = (4 : ℂ)))))).trans ((M.add_numbers (3 : ℂ) (4 : ℂ)).trans (congrArg M.number (by norm_num)))))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))).trans (congrArg M.number (by norm_num : (7 : ℂ) = (7 : ℂ)))).symm)))
      )
  )

theorem h_110 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (Litex.number (M := M) (3 : ℂ));
  let _wd_3_1 := (Litex.mul (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.numberInC (M := M) Complex.I));
  (Litex.add _wd_3_0 _wd_3_1 (Litex.numberInC (M := M) (3 : ℂ)) (by
    let _atomic_wd_1_0 := _wd_3_1
    exact (Litex.mulInC (Litex.number (M := M) (4 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
  (Litex.re _wd_2_0 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
  let _wd_1_1 := (let _wd_2_0 := (_wd_1_0).val.arg;
  (Litex.img _wd_2_0 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (_wd_1_1).val.arg;
    (Litex.re _wd_2_0 (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).val.right (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2))))
    exact (Litex.reInC _atomic_wd_1_0)) (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (_wd_1_1).val.arg;
    (Litex.img _wd_2_0 (by
      let _atomic_wd_2_0 := _wd_2_0
      exact (Litex.addInC (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).val.right (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2))))
    exact (Litex.imgInC _atomic_wd_1_0))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (7 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_55 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_complex_x5f_coordinate_x5f_arithmetic_x2f_statement_x2e_lit
