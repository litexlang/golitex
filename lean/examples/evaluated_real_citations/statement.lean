import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_real_x5f_citations_x2f_statement_x2e_lit

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

noncomputable def _object_i2 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
theorem h_33 : Litex.In (_object_i2 (M := M)) (Litex.R (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℝ) / (2 : ℝ)) (by norm_num))))
      )
  )
theorem h_34 : Litex.Same (_object_i2 (M := M)) (_object_i2 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
      )
  )

theorem h_89 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.min (_object_i1 (M := M)) (_object_i2 (M := M)) (h_13 (M := M)) (h_33 (M := M)));
  let _wd_1_1 := (Litex.ceil (_object_i1 (M := M)) (h_13 (M := M)));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (M.real_subset_complex _ (by
      let _extremum := _atomic_wd_1_0
      exact Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2
    ))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.roundingInZ _atomic_wd_1_0)))))
  let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (-13 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (-13 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.min (_object_i1 (M := M)) (_object_i2 (M := M)) (h_13 (M := M)) (h_33 (M := M)));
        let _wd_1_1 := (Litex.ceil (_object_i1 (M := M)) (h_13 (M := M)));
        (Litex.add _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (M.real_subset_complex _ (by
            let _extremum := _atomic_wd_1_0
            exact Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2
          ))) (by
          let _atomic_wd_1_0 := _wd_1_1
          exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.roundingInZ _atomic_wd_1_0)))));
        let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (-13 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (-13 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((congrArg₂ M.addValue (congrArg₂ (Litex.minMaxValue (M := M) false) (h_14 (M := M)) (h_34 (M := M))) (congrArg (Litex.roundingValue (M := M) true) (h_14 (M := M))))).trans (show (M.addValue ((Litex.minMaxValue (M := M) false) (M.divValue (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ))) (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ)))) ((Litex.roundingValue (M := M) true) (M.divValue (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ))))) = M.number ((-13 : ℂ) / (3 : ℂ)) from ((congrArg₂ M.addValue (show ((Litex.minMaxValue (M := M) false) (M.divValue (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ))) (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ)))) = M.number ((-7 : ℂ) / (3 : ℂ)) from (congrArg₂ (Litex.minMaxValue (M := M) false) (show (M.divValue (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ))) = M.number ((-7 : ℂ) / (3 : ℂ)) from ((congrArg₂ M.divValue (show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num))))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((M.div_numbers (-7 : ℂ) (3 : ℂ) (by norm_num)).trans (congrArg M.number (by norm_num))))) (show (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) = M.number ((1 : ℂ) / (2 : ℂ)) from ((congrArg₂ M.divValue (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num))) (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num)))).trans ((M.div_numbers (1 : ℂ) (2 : ℂ) (by norm_num)).trans (congrArg M.number (by norm_num)))))).trans (by
          have _numeric := Litex.minMaxValue_number false (M := M) ((-7 : ℝ) / (3 : ℝ)) ((1 : ℝ) / (2 : ℝ))
          norm_num [Real.sign] at _numeric
          simpa only [neg_div] using _numeric)) (show ((Litex.roundingValue (M := M) true) (M.divValue (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ)))) = M.number (-2 : ℂ) from (congrArg (Litex.roundingValue (M := M) true) (show (M.divValue (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ))) = M.number ((-7 : ℂ) / (3 : ℂ)) from ((congrArg₂ M.divValue (show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num))))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((M.div_numbers (-7 : ℂ) (3 : ℂ) (by norm_num)).trans (congrArg M.number (by norm_num)))))).trans (by
          have _numeric := Litex.roundingValue_number true (M := M) ((-7 : ℝ) / (3 : ℝ))
          norm_num [Real.sign] at _numeric
          simpa only [neg_div] using _numeric))).trans ((M.add_numbers ((-7 : ℂ) / (3 : ℂ)) (-2 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (-13 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (-13 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((-13 : ℂ) / (3 : ℂ)) = ((-13 : ℂ) / (3 : ℂ))))).symm)))
      )
  )

theorem h_155 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.min (_object_i1 (M := M)) (_object_i2 (M := M)) (h_13 (M := M)) (h_33 (M := M)));
  let _wd_1_1 := (Litex.ceil (_object_i1 (M := M)) (h_13 (M := M)));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (M.real_subset_complex _ (by
      let _extremum := _atomic_wd_1_0
      exact Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2
    ))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.roundingInZ _atomic_wd_1_0)))))
  let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (-13 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (-13 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (h_89 (M := M))
      )
  )

theorem h_197 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.sign (_object_i1 (M := M)) (h_13 (M := M)));
  let _wd_1_1 := (Litex.abs (_object_i1 (M := M)) (h_13 (M := M)));
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (M.real_subset_complex _ (by
      let _litex_abs := _atomic_wd_1_0
      exact Litex.absInR _litex_abs.val.arg _litex_abs.wd
    )))))
  let _equal_wd_1_1 := (_object_i1 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.sign (_object_i1 (M := M)) (h_13 (M := M)));
        let _wd_1_1 := (Litex.abs (_object_i1 (M := M)) (h_13 (M := M)));
        (Litex.mul _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0))) (by
          let _atomic_wd_1_0 := _wd_1_1
          exact (M.real_subset_complex _ (by
            let _litex_abs := _atomic_wd_1_0
            exact Litex.absInR _litex_abs.val.arg _litex_abs.wd
          )))));
        let _equal_wd_1_1 := (_object_i1 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((congrArg₂ M.mulValue (congrArg (Litex.signValue (M := M)) (h_14 (M := M))) (congrArg (Litex.absValue (M := M)) (h_14 (M := M))))).trans (show (M.mulValue ((Litex.signValue (M := M)) (M.divValue (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ)))) (Litex.absValue (M := M) (M.divValue (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ))))) = M.number ((-7 : ℂ) / (3 : ℂ)) from ((congrArg₂ M.mulValue (show ((Litex.signValue (M := M)) (M.divValue (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ)))) = M.number (-1 : ℂ) from (congrArg (Litex.signValue (M := M)) (show (M.divValue (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ))) = M.number ((-7 : ℂ) / (3 : ℂ)) from ((congrArg₂ M.divValue (show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num))))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((M.div_numbers (-7 : ℂ) (3 : ℂ) (by norm_num)).trans (congrArg M.number (by norm_num)))))).trans (by
          have _numeric := Litex.signValue_number (M := M) ((-7 : ℝ) / (3 : ℝ))
          norm_num [Real.sign] at _numeric
          simpa only [neg_div] using _numeric)) (show (Litex.absValue (M := M) (M.divValue (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ)))) = M.number ((7 : ℂ) / (3 : ℂ)) from (congrArg (Litex.absValue (M := M)) (show (M.divValue (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ))) = M.number ((-7 : ℂ) / (3 : ℂ)) from ((congrArg₂ M.divValue (show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num))))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((M.div_numbers (-7 : ℂ) (3 : ℂ) (by norm_num)).trans (congrArg M.number (by norm_num)))))).trans (by
          have _numeric := Litex.absValue_number (M := M) ((-7 : ℝ) / (3 : ℝ))
          norm_num [Real.sign] at _numeric
          simpa only [neg_div] using _numeric))).trans ((M.mul_numbers (-1 : ℂ) ((7 : ℂ) / (3 : ℂ))).trans (congrArg M.number (by norm_num)))))).trans (((Litex.NativeBridge.denoteDiv (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ))) (Litex.number (M := M) (3 : ℂ)) (by
          let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)))
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-7 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)))).trans (congrArg M.number (by norm_num : (- (7 : ℂ)) = (-7 : ℂ)))) (Litex.numberInC (M := M) (-7 : ℂ)))) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((- (7 : ℂ)) / (3 : ℂ)) = ((-7 : ℂ) / (3 : ℂ))))).symm)))
      )
  )

theorem h_238 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.sign (_object_i1 (M := M)) (h_13 (M := M)));
  let _wd_1_1 := (Litex.abs (_object_i1 (M := M)) (h_13 (M := M)));
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.signInZ _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (M.real_subset_complex _ (by
      let _litex_abs := _atomic_wd_1_0
      exact Litex.absInR _litex_abs.val.arg _litex_abs.wd
    )))))
  let _equal_wd_1_1 := (_object_i1 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (h_197 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_real_x5f_citations_x2f_statement_x2e_lit
