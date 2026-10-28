import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_integer_x5f_citations_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

noncomputable def _object_i1 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)))
theorem h_5 : Litex.In (_object_i1 (M := M)) (Litex.Z (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)))
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (7 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (7 : ℂ)) (-7 : ℤ) (by norm_num))))
      )
  )
theorem h_6 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ))))
      )
  )

noncomputable def _object_i2 := (Litex.number (M := M) (3 : ℂ))
theorem h_14 : Litex.In (_object_i2 (M := M)) (Litex.NPos (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.numberInNPosOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num) (by norm_num))
      )
  )
theorem h_15 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (_object_i2 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inNPos_positive (_object_i2 (M := M)) (h_14 (M := M)))
      )
  )
theorem h_16 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (_object_i2 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.ltToLe (Litex.number (M := M) 0) (_object_i2 (M := M)) (h_15 (M := M)))
      )
  )
theorem h_17 : ¬ Litex.Same (_object_i2 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) (_object_i2 (M := M)) (h_15 (M := M))) _litex_zero.symm)
      )
  )
theorem h_18 : Litex.Same (_object_i2 (M := M)) (Litex.number (M := M) (3 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.number (M := M) (3 : ℂ)))
      )
  )

theorem h_117 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.mod (_object_i1 (M := M)) (_object_i2 (M := M)) (h_5 (M := M)) (Litex.naturalToInteger (_object_i2 (M := M)) (Litex.inNPos_natural (_object_i2 (M := M)) (h_14 (M := M)))) (h_17 (M := M)));
  let _wd_1_1 := (Litex.quot (_object_i1 (M := M)) (_object_i2 (M := M)) (h_5 (M := M)) (h_14 (M := M)));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.modInZ _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.quotInZ _atomic_wd_1_0)))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (-1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.mod (_object_i1 (M := M)) (_object_i2 (M := M)) (h_5 (M := M)) (Litex.naturalToInteger (_object_i2 (M := M)) (Litex.inNPos_natural (_object_i2 (M := M)) (h_14 (M := M)))) (h_17 (M := M)));
        let _wd_1_1 := (Litex.quot (_object_i1 (M := M)) (_object_i2 (M := M)) (h_5 (M := M)) (h_14 (M := M)));
        (Litex.add _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.modInZ _atomic_wd_1_0))) (by
          let _atomic_wd_1_0 := _wd_1_1
          exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.quotInZ _atomic_wd_1_0)))));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (-1 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (-1 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (M.addValue ((Litex.integerDivisionValue (M := M) false) (Litex.denote (_object_i1 (M := M))) (Litex.denote (_object_i2 (M := M)))) ((Litex.integerDivisionValue (M := M) true) (Litex.denote (_object_i1 (M := M))) (Litex.denote (_object_i2 (M := M))))) from congrArg₂ M.addValue (show Litex.denote (_equal_wd_1_0).val.left = ((Litex.integerDivisionValue (M := M) false) (Litex.denote (_object_i1 (M := M))) (Litex.denote (_object_i2 (M := M)))) from congrArg₂ (Litex.integerDivisionValue (M := M) false) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl) (show Litex.denote (_object_i2 (M := M)) = (Litex.denote (_object_i2 (M := M))) from rfl)) (show Litex.denote (_equal_wd_1_0).val.right = ((Litex.integerDivisionValue (M := M) true) (Litex.denote (_object_i1 (M := M))) (Litex.denote (_object_i2 (M := M)))) from congrArg₂ (Litex.integerDivisionValue (M := M) true) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl) (show Litex.denote (_object_i2 (M := M)) = (Litex.denote (_object_i2 (M := M))) from rfl))) (((congrArg₂ M.addValue (congrArg₂ (Litex.integerDivisionValue (M := M) false) (Eq.trans (Eq.trans (Eq.symm (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl)) (h_6 (M := M))) (show Litex.denote (_object_i1 (M := M)) = (M.negValue (M.number (7 : ℂ))) from Eq.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)))).trans (congrArg M.number (by norm_num : (- (7 : ℂ)) = (-7 : ℂ)))) (Eq.symm (show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num)))))))) (Eq.trans (Eq.trans (Eq.symm (show Litex.denote (_object_i2 (M := M)) = (Litex.denote (_object_i2 (M := M))) from rfl)) (h_18 (M := M))) (show Litex.denote (Litex.number (M := M) (3 : ℂ)) = (M.number (3 : ℂ)) from rfl))) (congrArg₂ (Litex.integerDivisionValue (M := M) true) (Eq.trans (Eq.trans (Eq.symm (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl)) (h_6 (M := M))) (show Litex.denote (_object_i1 (M := M)) = (M.negValue (M.number (7 : ℂ))) from Eq.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)))).trans (congrArg M.number (by norm_num : (- (7 : ℂ)) = (-7 : ℂ)))) (Eq.symm (show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num)))))))) (Eq.trans (Eq.trans (Eq.symm (show Litex.denote (_object_i2 (M := M)) = (Litex.denote (_object_i2 (M := M))) from rfl)) (h_18 (M := M))) (show Litex.denote (Litex.number (M := M) (3 : ℂ)) = (M.number (3 : ℂ)) from rfl))))).trans (show (M.addValue ((Litex.integerDivisionValue (M := M) false) (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ))) ((Litex.integerDivisionValue (M := M) true) (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ)))) = M.number (-1 : ℂ) from ((congrArg₂ M.addValue (show ((Litex.integerDivisionValue (M := M) false) (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ))) = M.number (2 : ℂ) from (congrArg₂ (Litex.integerDivisionValue (M := M) false) (show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num))))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans (by
          have _numeric := Litex.integerDivisionValue_numbers false (M := M) (-7 : ℤ) (3 : ℤ)
          norm_num [Int.gcd_eq_natAbs_gcd_natAbs, Int.lcm_eq_natAbs_lcm_natAbs] at _numeric
          exact _numeric)) (show ((Litex.integerDivisionValue (M := M) true) (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ))) = M.number (-3 : ℂ) from (congrArg₂ (Litex.integerDivisionValue (M := M) true) (show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num))))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans (by
          have _numeric := Litex.integerDivisionValue_numbers true (M := M) (-7 : ℤ) (3 : ℤ)
          norm_num [Int.gcd_eq_natAbs_gcd_natAbs, Int.lcm_eq_natAbs_lcm_natAbs] at _numeric
          exact _numeric))).trans ((M.add_numbers (2 : ℂ) (-3 : ℂ)).trans (congrArg M.number (by norm_num)))))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))).trans (congrArg M.number (by norm_num : (-1 : ℂ) = (-1 : ℂ)))).symm)))
      )
  )

theorem h_216 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.mod (_object_i1 (M := M)) (_object_i2 (M := M)) (h_5 (M := M)) (Litex.naturalToInteger (_object_i2 (M := M)) (Litex.inNPos_natural (_object_i2 (M := M)) (h_14 (M := M)))) (h_17 (M := M)));
  let _wd_1_1 := (Litex.quot (_object_i1 (M := M)) (_object_i2 (M := M)) (h_5 (M := M)) (h_14 (M := M)));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.modInZ _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.quotInZ _atomic_wd_1_0)))))
  let _equal_wd_1_1 := (Litex.number (M := M) (-1 : ℂ))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (h_117 (M := M))
      )
  )

theorem h_1122 : (by
  let _equal_wd_1_0 := (Litex.gcd (_object_i1 (M := M)) (_object_i2 (M := M)) (h_5 (M := M)) (Litex.naturalToInteger (_object_i2 (M := M)) (Litex.inNPos_natural (_object_i2 (M := M)) (h_14 (M := M)))) (by
    classical
    apply Classical.byContradiction
    intro _negative_disjunction
    have h_1967 : Litex.Same (_object_i2 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Classical.byContradiction (fun _branch => _negative_disjunction (Or.inr _branch)))
          )
      )
    exact _negative_disjunction (Or.inl (Litex.notSameOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((h_6 (M := M))).symm (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) (by
      let _atomic_wd_2_0 := (_object_i1 (M := M))
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 (Litex.number (M := M) (0 : ℂ)) (- (7 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))))
  ))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (Litex.gcd (_object_i1 (M := M)) (_object_i2 (M := M)) (h_5 (M := M)) (Litex.naturalToInteger (_object_i2 (M := M)) (Litex.inNPos_natural (_object_i2 (M := M)) (h_14 (M := M)))) (by
          classical
          apply Classical.byContradiction
          intro _negative_disjunction
          have h_1967 : Litex.Same (_object_i2 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Classical.byContradiction (fun _branch => _negative_disjunction (Or.inr _branch)))
                )
            )
          exact _negative_disjunction (Or.inl (Litex.notSameOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((h_6 (M := M))).symm (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) (by
            let _atomic_wd_2_0 := (_object_i1 (M := M))
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 (Litex.number (M := M) (0 : ℂ)) (- (7 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))))
        ));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = ((Litex.gcdLcmValue (M := M) false) (Litex.denote (_object_i1 (M := M))) (Litex.denote (_object_i2 (M := M)))) from congrArg₂ (Litex.gcdLcmValue (M := M) false) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl) (show Litex.denote (_object_i2 (M := M)) = (Litex.denote (_object_i2 (M := M))) from rfl)) (((congrArg₂ (Litex.gcdLcmValue (M := M) false) (Eq.trans (Eq.trans (Eq.symm (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl)) (h_6 (M := M))) (show Litex.denote (_object_i1 (M := M)) = (M.negValue (M.number (7 : ℂ))) from Eq.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)))).trans (congrArg M.number (by norm_num : (- (7 : ℂ)) = (-7 : ℂ)))) (Eq.symm (show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num)))))))) (Eq.trans (Eq.trans (Eq.symm (show Litex.denote (_object_i2 (M := M)) = (Litex.denote (_object_i2 (M := M))) from rfl)) (h_18 (M := M))) (show Litex.denote (Litex.number (M := M) (3 : ℂ)) = (M.number (3 : ℂ)) from rfl)))).trans (show ((Litex.gcdLcmValue (M := M) false) (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ))) = M.number (1 : ℂ) from (congrArg₂ (Litex.gcdLcmValue (M := M) false) (show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num))))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans (by
          have _numeric := Litex.gcdLcmValue_numbers false (M := M) (-7 : ℤ) (3 : ℤ)
          norm_num [Int.gcd_eq_natAbs_gcd_natAbs, Int.lcm_eq_natAbs_lcm_natAbs] at _numeric
          exact _numeric))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))).symm)))
      )
  )

theorem h_2027 : (by
  let _equal_wd_1_0 := (Litex.gcd (_object_i1 (M := M)) (_object_i2 (M := M)) (h_5 (M := M)) (Litex.naturalToInteger (_object_i2 (M := M)) (Litex.inNPos_natural (_object_i2 (M := M)) (h_14 (M := M)))) (by
    classical
    apply Classical.byContradiction
    intro _negative_disjunction
    have h_1967 : Litex.Same (_object_i2 (M := M)) (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Classical.byContradiction (fun _branch => _negative_disjunction (Or.inr _branch)))
          )
      )
    exact _negative_disjunction (Or.inl (Litex.notSameOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((h_6 (M := M))).symm (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) (by
      let _atomic_wd_2_0 := (_object_i1 (M := M))
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 (Litex.number (M := M) (0 : ℂ)) (- (7 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))))
  ))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_1122 (M := M))
      )
  )

noncomputable def _object_i3 := (Litex.number (M := M) (5 : ℂ))
theorem h_2036 : Litex.In (_object_i3 (M := M)) (Litex.N (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.NativeBridge.numberInNOfEq (M := M) (5 : ℂ) (5 : ℕ) (by norm_num))
      )
  )
theorem h_2037 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (_object_i3 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.naturalNonnegative (_object_i3 (M := M)) (h_2036 (M := M)))
      )
  )
theorem h_2038 : Litex.Same (_object_i3 (M := M)) (Litex.number (M := M) (5 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.number (M := M) (5 : ℂ)))
      )
  )

theorem h_2048 : (by
  let _equal_wd_1_0 := (Litex.factorial (_object_i3 (M := M)) (h_2036 (M := M)))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (120 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (Litex.factorial (_object_i3 (M := M)) (h_2036 (M := M)));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (120 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (120 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = ((Litex.factorialValue (M := M)) (Litex.denote (_object_i3 (M := M)))) from congrArg (Litex.factorialValue (M := M)) (show Litex.denote (_object_i3 (M := M)) = (Litex.denote (_object_i3 (M := M))) from rfl)) (((congrArg (Litex.factorialValue (M := M)) (Eq.trans (Eq.trans (Eq.symm (show Litex.denote (_object_i3 (M := M)) = (Litex.denote (_object_i3 (M := M))) from rfl)) (h_2038 (M := M))) (show Litex.denote (Litex.number (M := M) (5 : ℂ)) = (M.number (5 : ℂ)) from rfl)))).trans (show ((Litex.factorialValue (M := M)) (M.number (5 : ℂ))) = M.number (120 : ℂ) from (congrArg (Litex.factorialValue (M := M)) (show (M.number (5 : ℂ)) = M.number (5 : ℂ) from (congrArg M.number (show (5 : ℂ) = (5 : ℂ) from by norm_num)))).trans (by
          have _numeric := Litex.factorialValue_number (M := M) (5 : ℕ)
          norm_num [Int.gcd_eq_natAbs_gcd_natAbs, Int.lcm_eq_natAbs_lcm_natAbs] at _numeric
          exact _numeric))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (120 : ℂ))).trans (congrArg M.number (by norm_num : (120 : ℂ) = (120 : ℂ)))).symm)))
      )
  )

theorem h_2058 : (by
  let _equal_wd_1_0 := (Litex.factorial (_object_i3 (M := M)) (h_2036 (M := M)))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (120 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_2048 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_integer_x5f_citations_x2f_statement_x2e_lit
