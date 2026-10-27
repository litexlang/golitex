import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_signed_x5f_representations_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

noncomputable def _object_i1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)));
let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
(Litex.div _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-7 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)))).trans (congrArg M.number (by norm_num : (- (7 : ℂ)) = (-7 : ℂ)))) (Litex.numberInC (M := M) (-7 : ℂ)))) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
theorem h_13 : Litex.In (_object_i1 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_2_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-7 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)))).trans (congrArg M.number (by norm_num : (- (7 : ℂ)) = (-7 : ℂ)))) (Litex.numberInC (M := M) (-7 : ℂ)))) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((- (7 : ℂ)) / (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (_atomic_wd_1_0).val.left (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) ((_atomic_wd_1_0).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((- (7 : ℂ)) / (3 : ℂ)) ((-7 : ℝ) / (3 : ℝ)) (by norm_num))))
      )
  )
theorem h_14 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)));
        let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
        (Litex.div _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-7 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)))).trans (congrArg M.number (by norm_num : (- (7 : ℂ)) = (-7 : ℂ)))) (Litex.numberInC (M := M) (-7 : ℂ)))) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))))
      )
  )

theorem h_15 : (by
  let _equal_wd_1_1 := (_object_i1 (M := M))
  exact Litex.Same (_object_i1 (M := M)) _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_1 := (_object_i1 (M := M));
        (show Litex.Same (_object_i1 (M := M)) _equal_wd_1_1 from (show Litex.Same (_object_i1 (M := M)) _equal_wd_1_1 from (((h_14 (M := M))).trans (show (M.divValue (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ))) = M.number ((-7 : ℂ) / (3 : ℂ)) from ((congrArg₂ M.divValue (show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num))))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((M.div_numbers (-7 : ℂ) (3 : ℂ) (by norm_num)).trans (congrArg M.number (by norm_num)))))).trans (((Litex.NativeBridge.denoteDiv (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ))) (Litex.number (M := M) (3 : ℂ)) (by
          let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)))
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-7 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)))).trans (congrArg M.number (by norm_num : (- (7 : ℂ)) = (-7 : ℂ)))) (Litex.numberInC (M := M) (-7 : ℂ)))) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((- (7 : ℂ)) / (3 : ℂ)) = ((-7 : ℂ) / (3 : ℂ))))).symm)))
      )
  )

theorem h_16 : (by
  let _equal_wd_1_1 := (_object_i1 (M := M))
  exact Litex.Same (_object_i1 (M := M)) _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (h_14 (M := M))
      )
  )

theorem h_31 : (by
  let _equal_wd_1_0 := (Litex.add (_object_i1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ (h_13 (M := M))) (Litex.numberInC (M := M) (1 : ℂ)))
  let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (-4 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (-4 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (Litex.add (_object_i1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ (h_13 (M := M))) (Litex.numberInC (M := M) (1 : ℂ)));
        let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (-4 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (-4 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((congrArg₂ M.addValue (h_14 (M := M)) (Eq.refl (M.number (1 : ℂ))))).trans (show (M.addValue (M.divValue (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ))) (M.number (1 : ℂ))) = M.number ((-4 : ℂ) / (3 : ℂ)) from ((congrArg₂ M.addValue (show (M.divValue (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ))) = M.number ((-7 : ℂ) / (3 : ℂ)) from ((congrArg₂ M.divValue (show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num))))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((M.div_numbers (-7 : ℂ) (3 : ℂ) (by norm_num)).trans (congrArg M.number (by norm_num))))) (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num)))).trans ((M.add_numbers ((-7 : ℂ) / (3 : ℂ)) (1 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (-4 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (-4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((-4 : ℂ) / (3 : ℂ)) = ((-4 : ℂ) / (3 : ℂ))))).symm)))
      )
  )

theorem h_52 : (by
  let _equal_wd_1_0 := (Litex.add (_object_i1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (M.real_subset_complex _ (h_13 (M := M))) (Litex.numberInC (M := M) (1 : ℂ)))
  let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (-4 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (-4 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (h_31 (M := M))
      )
  )

theorem h_59 : (by
  let _equal_wd_1_0 := (_object_i1 (M := M))
  let _equal_wd_1_1 := (_object_i1 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_i1 (M := M));
        let _equal_wd_1_1 := (_object_i1 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((Litex.NativeBridge.denoteDiv (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ))) (Litex.number (M := M) (3 : ℂ)) (by
          let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)))
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-7 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)))).trans (congrArg M.number (by norm_num : (- (7 : ℂ)) = (-7 : ℂ)))) (Litex.numberInC (M := M) (-7 : ℂ)))) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((- (7 : ℂ)) / (3 : ℂ)) = ((-7 : ℂ) / (3 : ℂ))))).trans (((Litex.NativeBridge.denoteDiv (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ))) (Litex.number (M := M) (3 : ℂ)) (by
          let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)))
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-7 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)))).trans (congrArg M.number (by norm_num : (- (7 : ℂ)) = (-7 : ℂ)))) (Litex.numberInC (M := M) (-7 : ℂ)))) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((- (7 : ℂ)) / (3 : ℂ)) = ((-7 : ℂ) / (3 : ℂ))))).symm)))
      )
  )

theorem h_60 : (by
  let _equal_wd_1_0 := (_object_i1 (M := M))
  let _equal_wd_1_1 := (_object_i1 (M := M))
  exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (show @Eq M.Value _ _ from Eq.refl _)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_signed_x5f_representations_x2f_statement_x2e_lit
