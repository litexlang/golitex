import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_imaginary_x5f_unit_x5f_values_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

theorem h_1 : Litex.In (Litex.number (M := M) Complex.I) (Litex.C (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.numberInC (M := M) Complex.I)
      )
  )

theorem h_2 : ¬ Litex.Same (Litex.number (M := M) Complex.I) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) Complex.I) (Litex.number (M := M) (0 : ℂ)) Complex.I (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) Complex.I) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num [Complex.ext_iff]))
      )
  )

noncomputable def _object_w4 := (Litex.mul (Litex.number (M := M) Complex.I) (Litex.number (M := M) Complex.I) (h_1 (M := M)) (h_1 (M := M)))

noncomputable def _object_w5 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)))

theorem h_3 : (by
  let _equal_wd_1_0 := (_object_w4 (M := M))
  let _equal_wd_1_1 := (_object_w5 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w4 (M := M));
        let _equal_wd_1_1 := (_object_w5 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Complex.I * Complex.I) (- (1 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) Complex.I) (Litex.number (M := M) Complex.I) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) Complex.I) (Litex.NativeBridge.denoteNumber (M := M) Complex.I)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_equal_wd_1_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by norm_num [Complex.ext_iff]))))
      )
  )

noncomputable def _object_w6 := (Litex.powNat (Litex.number (M := M) Complex.I) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (h_1 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))

theorem h_18 : (by
  let _equal_wd_1_0 := (_object_w6 (M := M))
  let _equal_wd_1_1 := (_object_w5 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w6 (M := M));
        let _equal_wd_1_1 := (_object_w5 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 _equal_wd_1_1 (Complex.I ^ (2 : ℕ)) (- (1 : ℂ)) (Litex.NativeBridge.denotePowNat (Litex.number (M := M) Complex.I) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (h_1 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) Complex.I)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) ((_object_w5 (M := M))).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by norm_num [Complex.ext_iff]))))
      )
  )

noncomputable def _object_w7 := (let _wd_1_0 := (Litex.add (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (1 : ℂ)) (h_1 (M := M)));
let _wd_1_1 := (Litex.sub (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (1 : ℂ)) (h_1 (M := M)));
(Litex.mul _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.addInC (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2)) (by
  let _atomic_wd_1_0 := _wd_1_1
  exact (Litex.subInC (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))))

theorem h_1807 : (by
  let _equal_wd_1_0 := (_object_w7 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w7 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (((1 : ℂ) + Complex.I) * ((1 : ℂ) - Complex.I)) (2 : ℂ) (Litex.NativeBridge.denoteMul (_equal_wd_1_0).val.left (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) Complex.I) ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) Complex.I)) (Litex.NativeBridge.denoteSub (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) Complex.I) ((_equal_wd_1_0).val.right).wd.1 ((_equal_wd_1_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) Complex.I))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num [Complex.ext_iff]))))
      )
  )

noncomputable def _object_w9 := (Litex.div (Litex.number (M := M) Complex.I) (Litex.number (M := M) Complex.I) (h_1 (M := M)) (h_1 (M := M)) (h_2 (M := M)))

theorem h_1847 : (by
  let _equal_wd_1_0 := (_object_w9 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w9 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) (Complex.I / Complex.I) (1 : ℂ) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) Complex.I) (Litex.number (M := M) Complex.I) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2.1 (_equal_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) Complex.I) (Litex.NativeBridge.denoteNumber (M := M) Complex.I)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (by norm_num [Complex.ext_iff]))))
      )
  )

noncomputable def _object_w11 := (let _wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (1 : ℂ)) (h_1 (M := M)) (h_2 (M := M)));
let _wd_1_1 := (Litex.number (M := M) Complex.I);
(Litex.add _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.divInC (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2)) (h_1 (M := M))))

theorem h_1864 : (by
  let _equal_wd_1_0 := (_object_w11 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w11 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (((1 : ℂ) / Complex.I) + Complex.I) (0 : ℂ) (Litex.NativeBridge.denoteAdd (_equal_wd_1_0).val.left (Litex.number (M := M) Complex.I) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) Complex.I) ((_equal_wd_1_0).val.left).wd.1 ((_equal_wd_1_0).val.left).wd.2.1 ((_equal_wd_1_0).val.left).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) Complex.I)) (Litex.NativeBridge.denoteNumber (M := M) Complex.I)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num [Complex.ext_iff]))))
      )
  )

noncomputable def _object_i1 := ((_object_w7 (M := M))).val.left
theorem h_1908 : Litex.Same (_object_i1 (M := M)) ((_object_w7 (M := M))).val.left :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl ((_object_w7 (M := M))).val.left)
      )
  )

theorem h_1909 : (by
  let _equal_wd_1_1 := ((_object_w7 (M := M))).val.left
  exact Litex.Same (_object_i1 (M := M)) _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (h_1908 (M := M))
      )
  )

noncomputable def _object_w13 := (let _wd_1_0 := (_object_i1 (M := M));
let _wd_1_1 := ((_object_w7 (M := M))).val.right;
(Litex.mul _wd_1_0 _wd_1_1 (Litex.inOfSame ((_object_w7 (M := M))).val.left _wd_1_0 (Litex.C (M := M)) (Litex.C (M := M)) ((((Litex.sameRefl _wd_1_0)).trans (h_1908 (M := M)))).symm (Litex.sameRefl (Litex.C (M := M))) (by
  let _atomic_wd_2_0 := ((_object_w7 (M := M))).val.left
  exact (Litex.addInC (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) (1 : ℂ)) (h_1 (M := M))))) (by
  let _atomic_wd_1_0 := _wd_1_1
  exact (Litex.subInC (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) Complex.I) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2))))

theorem h_1911 : (by
  let _equal_wd_1_0 := (_object_w13 (M := M))
  let _equal_wd_1_1 := (_object_w7 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (congrArg₂ M.mulValue (show (Litex.denote (_object_i1 (M := M))) = (M.addValue (M.number (1 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))) from (h_1908 (M := M))) (show (M.subValue (M.number (1 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))) = (M.subValue (M.number (1 : ℂ)) (Litex.denote (Litex.number (M := M) Complex.I))) from (show @Eq M.Value _ _ from Eq.refl _)))
      )
  )

theorem h_3060 : (by
  let _equal_wd_1_0 := (_object_w13 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (((h_1911 (M := M))).trans (h_1807 (M := M)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_imaginary_x5f_unit_x5f_values_x2f_statement_x2e_lit
