import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_integer_x5f_operations_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_2 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (54 : ℂ));
  let _wd_1_1 := (Litex.neg (Litex.number (M := M) (24 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (24 : ℂ)) (24 : ℂ) Litex.C (show (M.number (24 : ℂ)) = M.number (24 : ℂ) from (congrArg M.number (show (24 : ℂ) = (24 : ℂ) from by norm_num))) (Litex.numberInC (24 : ℂ))));
  (Litex.gcd _wd_1_0 _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_0 ((54 : ℤ) : ℂ) Litex.Z (((Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ))).trans (congrArg M.number (by norm_num : (54 : ℂ) = ((54 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (54))) (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 ((-24 : ℤ) : ℂ) Litex.Z (((show (M.negValue (M.number (24 : ℂ))) = M.number (-24 : ℂ) from ((congrArg M.negValue (show (M.number (24 : ℂ)) = M.number (24 : ℂ) from (congrArg M.number (show (24 : ℂ) = (24 : ℂ) from by norm_num)))).trans ((M.neg_numbers (24 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-24 : ℂ) = ((-24 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (-24))) (Or.inl (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_0 (Litex.number 0) ((54 : ℤ) : ℂ) 0 (((Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ))).trans (congrArg M.number (by norm_num : (54 : ℂ) = ((54 : ℤ) : ℂ)))) rfl (by norm_num)))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (54 : ℂ));
        let _wd_1_1 := (Litex.neg (Litex.number (M := M) (24 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (24 : ℂ)) (24 : ℂ) Litex.C (show (M.number (24 : ℂ)) = M.number (24 : ℂ) from (congrArg M.number (show (24 : ℂ) = (24 : ℂ) from by norm_num))) (Litex.numberInC (24 : ℂ))));
        (Litex.gcd _wd_1_0 _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_0 ((54 : ℤ) : ℂ) Litex.Z (((Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ))).trans (congrArg M.number (by norm_num : (54 : ℂ) = ((54 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (54))) (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 ((-24 : ℤ) : ℂ) Litex.Z (((show (M.negValue (M.number (24 : ℂ))) = M.number (-24 : ℂ) from ((congrArg M.negValue (show (M.number (24 : ℂ)) = M.number (24 : ℂ) from (congrArg M.number (show (24 : ℂ) = (24 : ℂ) from by norm_num)))).trans ((M.neg_numbers (24 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-24 : ℂ) = ((-24 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (-24))) (Or.inl (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_0 (Litex.number 0) ((54 : ℤ) : ℂ) 0 (((Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ))).trans (congrArg M.number (by norm_num : (54 : ℂ) = ((54 : ℤ) : ℂ)))) rfl (by norm_num)))));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) from (((let _intop := _equal_wd_1_0;
        let _member : Litex.In _intop Litex.C := Litex.naturalToComplex _intop (Litex.gcdInN _intop);
        (Litex.gcdDenoteInt _intop (54 : ℤ) (-24 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ))).trans (congrArg M.number (by norm_num : (54 : ℂ) = ((54 : ℤ) : ℂ)))) (((show (M.negValue (M.number (24 : ℂ))) = M.number (-24 : ℂ) from ((congrArg M.negValue (show (M.number (24 : ℂ)) = M.number (24 : ℂ) from (congrArg M.number (show (24 : ℂ) = (24 : ℂ) from by norm_num)))).trans ((M.neg_numbers (24 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-24 : ℂ) = ((-24 : ℤ) : ℂ))))).trans (congrArg M.number (by norm_num [Int.gcd_eq_natAbs_gcd_natAbs])))).trans (congrArg M.number (by norm_num : (6 : ℂ) = (6 : ℂ)))).trans (((Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))).trans (congrArg M.number (by norm_num : (6 : ℂ) = (6 : ℂ)))).symm)))
      )
  )

theorem h_3 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (54 : ℂ));
  let _wd_1_1 := (Litex.neg (Litex.number (M := M) (24 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (24 : ℂ)) (24 : ℂ) Litex.C (show (M.number (24 : ℂ)) = M.number (24 : ℂ) from (congrArg M.number (show (24 : ℂ) = (24 : ℂ) from by norm_num))) (Litex.numberInC (24 : ℂ))));
  (Litex.gcd _wd_1_0 _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_0 ((54 : ℤ) : ℂ) Litex.Z (((Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ))).trans (congrArg M.number (by norm_num : (54 : ℂ) = ((54 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (54))) (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 ((-24 : ℤ) : ℂ) Litex.Z (((show (M.negValue (M.number (24 : ℂ))) = M.number (-24 : ℂ) from ((congrArg M.negValue (show (M.number (24 : ℂ)) = M.number (24 : ℂ) from (congrArg M.number (show (24 : ℂ) = (24 : ℂ) from by norm_num)))).trans ((M.neg_numbers (24 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-24 : ℂ) = ((-24 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (-24))) (Or.inl (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_0 (Litex.number 0) ((54 : ℤ) : ℂ) 0 (((Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ))).trans (congrArg M.number (by norm_num : (54 : ℂ) = ((54 : ℤ) : ℂ)))) rfl (by norm_num)))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_2 (M := M))
      )
  )

theorem h_6 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (0 : ℂ));
  let _wd_1_1 := (Litex.neg (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (9 : ℂ)) (9 : ℂ) Litex.C (show (M.number (9 : ℂ)) = M.number (9 : ℂ) from (congrArg M.number (show (9 : ℂ) = (9 : ℂ) from by norm_num))) (Litex.numberInC (9 : ℂ))));
  (Litex.gcd _wd_1_0 _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_0 ((0 : ℤ) : ℂ) Litex.Z (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (0))) (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 ((-9 : ℤ) : ℂ) Litex.Z (((show (M.negValue (M.number (9 : ℂ))) = M.number (-9 : ℂ) from ((congrArg M.negValue (show (M.number (9 : ℂ)) = M.number (9 : ℂ) from (congrArg M.number (show (9 : ℂ) = (9 : ℂ) from by norm_num)))).trans ((M.neg_numbers (9 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-9 : ℂ) = ((-9 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (-9))) (Or.inr (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number 0) ((-9 : ℤ) : ℂ) 0 (((show (M.negValue (M.number (9 : ℂ))) = M.number (-9 : ℂ) from ((congrArg M.negValue (show (M.number (9 : ℂ)) = M.number (9 : ℂ) from (congrArg M.number (show (9 : ℂ) = (9 : ℂ) from by norm_num)))).trans ((M.neg_numbers (9 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-9 : ℂ) = ((-9 : ℤ) : ℂ)))) rfl (by norm_num)))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (9 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (0 : ℂ));
        let _wd_1_1 := (Litex.neg (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (9 : ℂ)) (9 : ℂ) Litex.C (show (M.number (9 : ℂ)) = M.number (9 : ℂ) from (congrArg M.number (show (9 : ℂ) = (9 : ℂ) from by norm_num))) (Litex.numberInC (9 : ℂ))));
        (Litex.gcd _wd_1_0 _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_0 ((0 : ℤ) : ℂ) Litex.Z (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (0))) (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 ((-9 : ℤ) : ℂ) Litex.Z (((show (M.negValue (M.number (9 : ℂ))) = M.number (-9 : ℂ) from ((congrArg M.negValue (show (M.number (9 : ℂ)) = M.number (9 : ℂ) from (congrArg M.number (show (9 : ℂ) = (9 : ℂ) from by norm_num)))).trans ((M.neg_numbers (9 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-9 : ℂ) = ((-9 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (-9))) (Or.inr (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number 0) ((-9 : ℤ) : ℂ) 0 (((show (M.negValue (M.number (9 : ℂ))) = M.number (-9 : ℂ) from ((congrArg M.negValue (show (M.number (9 : ℂ)) = M.number (9 : ℂ) from (congrArg M.number (show (9 : ℂ) = (9 : ℂ) from by norm_num)))).trans ((M.neg_numbers (9 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-9 : ℂ) = ((-9 : ℤ) : ℂ)))) rfl (by norm_num)))));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (9 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (9 : ℂ)) from (((let _intop := _equal_wd_1_0;
        let _member : Litex.In _intop Litex.C := Litex.naturalToComplex _intop (Litex.gcdInN _intop);
        (Litex.gcdDenoteInt _intop (0 : ℤ) (-9 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (((show (M.negValue (M.number (9 : ℂ))) = M.number (-9 : ℂ) from ((congrArg M.negValue (show (M.number (9 : ℂ)) = M.number (9 : ℂ) from (congrArg M.number (show (9 : ℂ) = (9 : ℂ) from by norm_num)))).trans ((M.neg_numbers (9 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-9 : ℂ) = ((-9 : ℤ) : ℂ))))).trans (congrArg M.number (by norm_num [Int.gcd_eq_natAbs_gcd_natAbs])))).trans (congrArg M.number (by norm_num : (9 : ℂ) = (9 : ℂ)))).trans (((Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))).trans (congrArg M.number (by norm_num : (9 : ℂ) = (9 : ℂ)))).symm)))
      )
  )

theorem h_7 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (0 : ℂ));
  let _wd_1_1 := (Litex.neg (Litex.number (M := M) (9 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (9 : ℂ)) (9 : ℂ) Litex.C (show (M.number (9 : ℂ)) = M.number (9 : ℂ) from (congrArg M.number (show (9 : ℂ) = (9 : ℂ) from by norm_num))) (Litex.numberInC (9 : ℂ))));
  (Litex.gcd _wd_1_0 _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_0 ((0 : ℤ) : ℂ) Litex.Z (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (0))) (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 ((-9 : ℤ) : ℂ) Litex.Z (((show (M.negValue (M.number (9 : ℂ))) = M.number (-9 : ℂ) from ((congrArg M.negValue (show (M.number (9 : ℂ)) = M.number (9 : ℂ) from (congrArg M.number (show (9 : ℂ) = (9 : ℂ) from by norm_num)))).trans ((M.neg_numbers (9 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-9 : ℂ) = ((-9 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (-9))) (Or.inr (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number 0) ((-9 : ℤ) : ℂ) 0 (((show (M.negValue (M.number (9 : ℂ))) = M.number (-9 : ℂ) from ((congrArg M.negValue (show (M.number (9 : ℂ)) = M.number (9 : ℂ) from (congrArg M.number (show (9 : ℂ) = (9 : ℂ) from by norm_num)))).trans ((M.neg_numbers (9 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-9 : ℂ) = ((-9 : ℤ) : ℂ)))) rfl (by norm_num)))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (9 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_6 (M := M))
      )
  )

theorem h_10 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (6 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (6 : ℂ)) (6 : ℂ) Litex.C (show (M.number (6 : ℂ)) = M.number (6 : ℂ) from (congrArg M.number (show (6 : ℂ) = (6 : ℂ) from by norm_num))) (Litex.numberInC (6 : ℂ))));
  let _wd_1_1 := (Litex.number (M := M) (15 : ℂ));
  (Litex.lcm _wd_1_0 _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_0 ((-6 : ℤ) : ℂ) Litex.Z (((show (M.negValue (M.number (6 : ℂ))) = M.number (-6 : ℂ) from ((congrArg M.negValue (show (M.number (6 : ℂ)) = M.number (6 : ℂ) from (congrArg M.number (show (6 : ℂ) = (6 : ℂ) from by norm_num)))).trans ((M.neg_numbers (6 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-6 : ℂ) = ((-6 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (-6))) (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 ((15 : ℤ) : ℂ) Litex.Z (((Litex.NativeBridge.denoteNumber (M := M) (15 : ℂ))).trans (congrArg M.number (by norm_num : (15 : ℂ) = ((15 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (15)))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (30 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (6 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (6 : ℂ)) (6 : ℂ) Litex.C (show (M.number (6 : ℂ)) = M.number (6 : ℂ) from (congrArg M.number (show (6 : ℂ) = (6 : ℂ) from by norm_num))) (Litex.numberInC (6 : ℂ))));
        let _wd_1_1 := (Litex.number (M := M) (15 : ℂ));
        (Litex.lcm _wd_1_0 _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_0 ((-6 : ℤ) : ℂ) Litex.Z (((show (M.negValue (M.number (6 : ℂ))) = M.number (-6 : ℂ) from ((congrArg M.negValue (show (M.number (6 : ℂ)) = M.number (6 : ℂ) from (congrArg M.number (show (6 : ℂ) = (6 : ℂ) from by norm_num)))).trans ((M.neg_numbers (6 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-6 : ℂ) = ((-6 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (-6))) (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 ((15 : ℤ) : ℂ) Litex.Z (((Litex.NativeBridge.denoteNumber (M := M) (15 : ℂ))).trans (congrArg M.number (by norm_num : (15 : ℂ) = ((15 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (15)))));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (30 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (30 : ℂ)) from (((let _intop := _equal_wd_1_0;
        let _member : Litex.In _intop Litex.C := Litex.naturalToComplex _intop (Litex.lcmInN _intop);
        (Litex.lcmDenoteInt _intop (-6 : ℤ) (15 : ℤ) (((show (M.negValue (M.number (6 : ℂ))) = M.number (-6 : ℂ) from ((congrArg M.negValue (show (M.number (6 : ℂ)) = M.number (6 : ℂ) from (congrArg M.number (show (6 : ℂ) = (6 : ℂ) from by norm_num)))).trans ((M.neg_numbers (6 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-6 : ℂ) = ((-6 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (15 : ℂ))).trans (congrArg M.number (by norm_num : (15 : ℂ) = ((15 : ℤ) : ℂ))))).trans (congrArg M.number (by norm_num [Int.lcm_eq_natAbs_lcm_natAbs])))).trans (congrArg M.number (by norm_num : (30 : ℂ) = (30 : ℂ)))).trans (((Litex.NativeBridge.denoteNumber (M := M) (30 : ℂ))).trans (congrArg M.number (by norm_num : (30 : ℂ) = (30 : ℂ)))).symm)))
      )
  )

theorem h_11 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (6 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (6 : ℂ)) (6 : ℂ) Litex.C (show (M.number (6 : ℂ)) = M.number (6 : ℂ) from (congrArg M.number (show (6 : ℂ) = (6 : ℂ) from by norm_num))) (Litex.numberInC (6 : ℂ))));
  let _wd_1_1 := (Litex.number (M := M) (15 : ℂ));
  (Litex.lcm _wd_1_0 _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_0 ((-6 : ℤ) : ℂ) Litex.Z (((show (M.negValue (M.number (6 : ℂ))) = M.number (-6 : ℂ) from ((congrArg M.negValue (show (M.number (6 : ℂ)) = M.number (6 : ℂ) from (congrArg M.number (show (6 : ℂ) = (6 : ℂ) from by norm_num)))).trans ((M.neg_numbers (6 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-6 : ℂ) = ((-6 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (-6))) (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 ((15 : ℤ) : ℂ) Litex.Z (((Litex.NativeBridge.denoteNumber (M := M) (15 : ℂ))).trans (congrArg M.number (by norm_num : (15 : ℂ) = ((15 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (15)))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (30 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_10 (M := M))
      )
  )

theorem h_14 : (by
  let _equal_wd_1_0 := (Litex.lcm (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) ((0 : ℤ) : ℂ) Litex.Z (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (0))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) ((0 : ℤ) : ℂ) Litex.Z (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (0))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (Litex.lcm (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) ((0 : ℤ) : ℂ) Litex.Z (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (0))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) ((0 : ℤ) : ℂ) Litex.Z (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (0))));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ)) from (((let _intop := _equal_wd_1_0;
        let _member : Litex.In _intop Litex.C := Litex.naturalToComplex _intop (Litex.lcmInN _intop);
        (Litex.lcmDenoteInt _intop (0 : ℤ) (0 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ))))).trans (congrArg M.number (by norm_num [Int.lcm_eq_natAbs_lcm_natAbs])))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))).trans (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))).symm)))
      )
  )

theorem h_15 : (by
  let _equal_wd_1_0 := (Litex.lcm (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) ((0 : ℤ) : ℂ) Litex.Z (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (0))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) ((0 : ℤ) : ℂ) Litex.Z (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (0))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_14 (M := M))
      )
  )

theorem h_20 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (7 : ℂ)) (7 : ℂ) Litex.C (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num))) (Litex.numberInC (7 : ℂ))));
  let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
  (let _eval_divisor_nonzero := (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num));
  Litex.mod _wd_1_0 _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_0 ((-7 : ℤ) : ℂ) Litex.Z (((show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-7 : ℂ) = ((-7 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (-7))) (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 ((3 : ℤ) : ℂ) Litex.Z (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = ((3 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (3))) _eval_divisor_nonzero))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (7 : ℂ)) (7 : ℂ) Litex.C (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num))) (Litex.numberInC (7 : ℂ))));
        let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
        (let _eval_divisor_nonzero := (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num));
        Litex.mod _wd_1_0 _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_0 ((-7 : ℤ) : ℂ) Litex.Z (((show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-7 : ℂ) = ((-7 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (-7))) (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 ((3 : ℤ) : ℂ) Litex.Z (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = ((3 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (3))) _eval_divisor_nonzero));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from (((let _intop := _equal_wd_1_0;
        let _member : Litex.In _intop Litex.C := Litex.integerToComplex _intop (Litex.modInZ _intop);
        (Litex.modDenoteInt _intop (-7 : ℤ) (3 : ℤ) (((show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-7 : ℂ) = ((-7 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = ((3 : ℤ) : ℂ))))).trans (congrArg M.number (by norm_num)))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))).trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))).symm)))
      )
  )

theorem h_22 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (7 : ℂ)) (7 : ℂ) Litex.C (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num))) (Litex.numberInC (7 : ℂ))));
  let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
  (let _eval_divisor_nonzero := (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num));
  Litex.mod _wd_1_0 _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_0 ((-7 : ℤ) : ℂ) Litex.Z (((show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-7 : ℂ) = ((-7 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (-7))) (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 ((3 : ℤ) : ℂ) Litex.Z (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = ((3 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (3))) _eval_divisor_nonzero))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_20 (M := M))
      )
  )

theorem h_27 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (7 : ℂ)) (7 : ℂ) Litex.C (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num))) (Litex.numberInC (7 : ℂ))));
  let _wd_1_1 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) Litex.C (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num))) (Litex.numberInC (3 : ℂ))));
  (let _eval_divisor_nonzero := (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (-3 : ℂ) (0 : ℂ) (show (M.negValue (M.number (3 : ℂ))) = M.number (-3 : ℂ) from ((congrArg M.negValue (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((M.neg_numbers (3 : ℂ)).trans (congrArg M.number (by norm_num))))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  Litex.mod _wd_1_0 _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_0 ((-7 : ℤ) : ℂ) Litex.Z (((show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-7 : ℂ) = ((-7 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (-7))) (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 ((-3 : ℤ) : ℂ) Litex.Z (((show (M.negValue (M.number (3 : ℂ))) = M.number (-3 : ℂ) from ((congrArg M.negValue (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((M.neg_numbers (3 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = ((-3 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (-3))) _eval_divisor_nonzero))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (7 : ℂ)) (7 : ℂ) Litex.C (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num))) (Litex.numberInC (7 : ℂ))));
        let _wd_1_1 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) Litex.C (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num))) (Litex.numberInC (3 : ℂ))));
        (let _eval_divisor_nonzero := (by
          let _atomic_wd_1_0 := _wd_1_1
          exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (-3 : ℂ) (0 : ℂ) (show (M.negValue (M.number (3 : ℂ))) = M.number (-3 : ℂ) from ((congrArg M.negValue (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((M.neg_numbers (3 : ℂ)).trans (congrArg M.number (by norm_num))))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        Litex.mod _wd_1_0 _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_0 ((-7 : ℤ) : ℂ) Litex.Z (((show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-7 : ℂ) = ((-7 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (-7))) (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 ((-3 : ℤ) : ℂ) Litex.Z (((show (M.negValue (M.number (3 : ℂ))) = M.number (-3 : ℂ) from ((congrArg M.negValue (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((M.neg_numbers (3 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = ((-3 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (-3))) _eval_divisor_nonzero));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from (((let _intop := _equal_wd_1_0;
        let _member : Litex.In _intop Litex.C := Litex.integerToComplex _intop (Litex.modInZ _intop);
        (Litex.modDenoteInt _intop (-7 : ℤ) (-3 : ℤ) (((show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-7 : ℂ) = ((-7 : ℤ) : ℂ)))) (((show (M.negValue (M.number (3 : ℂ))) = M.number (-3 : ℂ) from ((congrArg M.negValue (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((M.neg_numbers (3 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = ((-3 : ℤ) : ℂ))))).trans (congrArg M.number (by norm_num)))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))).trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))).symm)))
      )
  )

theorem h_29 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (7 : ℂ)) (7 : ℂ) Litex.C (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num))) (Litex.numberInC (7 : ℂ))));
  let _wd_1_1 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) Litex.C (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num))) (Litex.numberInC (3 : ℂ))));
  (let _eval_divisor_nonzero := (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (-3 : ℂ) (0 : ℂ) (show (M.negValue (M.number (3 : ℂ))) = M.number (-3 : ℂ) from ((congrArg M.negValue (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((M.neg_numbers (3 : ℂ)).trans (congrArg M.number (by norm_num))))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  Litex.mod _wd_1_0 _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_0 ((-7 : ℤ) : ℂ) Litex.Z (((show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-7 : ℂ) = ((-7 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (-7))) (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 ((-3 : ℤ) : ℂ) Litex.Z (((show (M.negValue (M.number (3 : ℂ))) = M.number (-3 : ℂ) from ((congrArg M.negValue (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((M.neg_numbers (3 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = ((-3 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (-3))) _eval_divisor_nonzero))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_27 (M := M))
      )
  )

theorem h_34 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (7 : ℂ)) (7 : ℂ) Litex.C (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num))) (Litex.numberInC (7 : ℂ))));
  let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
  (let _eval_divisor_nonzero := (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num));
  Litex.quot _wd_1_0 _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_0 ((-7 : ℤ) : ℂ) Litex.Z (((show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-7 : ℂ) = ((-7 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (-7))) (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 ((3 : ℕ) : ℂ) Litex.NPos (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = ((3 : ℕ) : ℂ)))) (Litex.numberInNPosOfEq ((3 : ℕ) : ℂ) 3 rfl (by norm_num)))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (-3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (7 : ℂ)) (7 : ℂ) Litex.C (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num))) (Litex.numberInC (7 : ℂ))));
        let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
        (let _eval_divisor_nonzero := (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num));
        Litex.quot _wd_1_0 _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_0 ((-7 : ℤ) : ℂ) Litex.Z (((show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-7 : ℂ) = ((-7 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (-7))) (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 ((3 : ℕ) : ℂ) Litex.NPos (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = ((3 : ℕ) : ℂ)))) (Litex.numberInNPosOfEq ((3 : ℕ) : ℂ) 3 rfl (by norm_num)))));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (-3 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (-3 : ℂ)) from (((let _intop := _equal_wd_1_0;
        let _member : Litex.In _intop Litex.C := Litex.integerToComplex _intop (Litex.quotInZ _intop);
        (Litex.quotDenoteInt _intop (-7 : ℤ) (3 : ℤ) (((show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-7 : ℂ) = ((-7 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = ((3 : ℤ) : ℂ))))).trans (congrArg M.number (by norm_num)))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))).trans (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))).symm)))
      )
  )

theorem h_36 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (7 : ℂ)) (7 : ℂ) Litex.C (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num))) (Litex.numberInC (7 : ℂ))));
  let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
  (let _eval_divisor_nonzero := (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num));
  Litex.quot _wd_1_0 _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_0 ((-7 : ℤ) : ℂ) Litex.Z (((show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans (congrArg M.number (by norm_num : (-7 : ℂ) = ((-7 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (-7))) (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 ((3 : ℕ) : ℂ) Litex.NPos (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = ((3 : ℕ) : ℂ)))) (Litex.numberInNPosOfEq ((3 : ℕ) : ℂ) 3 rfl (by norm_num)))))
  let _equal_wd_1_1 := (Litex.number (M := M) (-3 : ℂ))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (h_34 (M := M))
      )
  )

theorem h_39 : (by
  let _equal_wd_1_0 := (Litex.factorial (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) ((0 : ℕ) : ℂ) Litex.N (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℕ) : ℂ)))) (Litex.NativeBridge.numberInN (0))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (Litex.factorial (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) ((0 : ℕ) : ℂ) Litex.N (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℕ) : ℂ)))) (Litex.NativeBridge.numberInN (0))));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (((let _factorial := _equal_wd_1_0;
        let _member : Litex.In _factorial Litex.C := Litex.naturalToComplex _factorial (Litex.factorialInN _factorial);
        (Litex.factorialDenoteNat _factorial 0 (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℕ) : ℂ))))).trans (congrArg M.number (by norm_num)))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))).trans (((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))).symm)))
      )
  )

theorem h_40 : (by
  let _equal_wd_1_0 := (Litex.factorial (Litex.number (M := M) (0 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (0 : ℂ)) ((0 : ℕ) : ℂ) Litex.N (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = ((0 : ℕ) : ℂ)))) (Litex.NativeBridge.numberInN (0))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_39 (M := M))
      )
  )

theorem h_43 : (by
  let _equal_wd_1_0 := (Litex.factorial (Litex.number (M := M) (6 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (6 : ℂ)) ((6 : ℕ) : ℂ) Litex.N (((Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))).trans (congrArg M.number (by norm_num : (6 : ℂ) = ((6 : ℕ) : ℂ)))) (Litex.NativeBridge.numberInN (6))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (720 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (Litex.factorial (Litex.number (M := M) (6 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (6 : ℂ)) ((6 : ℕ) : ℂ) Litex.N (((Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))).trans (congrArg M.number (by norm_num : (6 : ℂ) = ((6 : ℕ) : ℂ)))) (Litex.NativeBridge.numberInN (6))));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (720 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (720 : ℂ)) from (((let _factorial := _equal_wd_1_0;
        let _member : Litex.In _factorial Litex.C := Litex.naturalToComplex _factorial (Litex.factorialInN _factorial);
        (Litex.factorialDenoteNat _factorial 6 (((Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))).trans (congrArg M.number (by norm_num : (6 : ℂ) = ((6 : ℕ) : ℂ))))).trans (congrArg M.number (by norm_num)))).trans (congrArg M.number (by norm_num : (720 : ℂ) = (720 : ℂ)))).trans (((Litex.NativeBridge.denoteNumber (M := M) (720 : ℂ))).trans (congrArg M.number (by norm_num : (720 : ℂ) = (720 : ℂ)))).symm)))
      )
  )

theorem h_44 : (by
  let _equal_wd_1_0 := (Litex.factorial (Litex.number (M := M) (6 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (6 : ℂ)) ((6 : ℕ) : ℂ) Litex.N (((Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))).trans (congrArg M.number (by norm_num : (6 : ℂ) = ((6 : ℕ) : ℂ)))) (Litex.NativeBridge.numberInN (6))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (720 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_43 (M := M))
      )
  )

theorem h_47 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.factorial (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (5 : ℂ)) ((5 : ℕ) : ℂ) Litex.N (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = ((5 : ℕ) : ℂ)))) (Litex.NativeBridge.numberInN (5))));
  let _wd_1_1 := (Litex.lcm (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (18 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) ((12 : ℤ) : ℂ) Litex.Z (((Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))).trans (congrArg M.number (by norm_num : (12 : ℂ) = ((12 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (12))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (18 : ℂ)) ((18 : ℤ) : ℂ) Litex.Z (((Litex.NativeBridge.denoteNumber (M := M) (18 : ℂ))).trans (congrArg M.number (by norm_num : (18 : ℂ) = ((18 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (18))));
  (Litex.gcd _wd_1_0 _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_0 ((120 : ℤ) : ℂ) Litex.Z (((let _factorial := _wd_1_0;
  let _member : Litex.In _factorial Litex.C := Litex.naturalToComplex _factorial (Litex.factorialInN _factorial);
  (Litex.factorialDenoteNat _factorial 5 (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = ((5 : ℕ) : ℂ))))).trans (congrArg M.number (by norm_num)))).trans (congrArg M.number (by norm_num : (120 : ℂ) = ((120 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (120))) (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 ((36 : ℤ) : ℂ) Litex.Z (((let _intop := _wd_1_1;
  let _member : Litex.In _intop Litex.C := Litex.naturalToComplex _intop (Litex.lcmInN _intop);
  (Litex.lcmDenoteInt _intop (12 : ℤ) (18 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))).trans (congrArg M.number (by norm_num : (12 : ℂ) = ((12 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (18 : ℂ))).trans (congrArg M.number (by norm_num : (18 : ℂ) = ((18 : ℤ) : ℂ))))).trans (congrArg M.number (by norm_num [Int.lcm_eq_natAbs_lcm_natAbs])))).trans (congrArg M.number (by norm_num : (36 : ℂ) = ((36 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (36))) (Or.inl (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_0 (Litex.number 0) ((120 : ℤ) : ℂ) 0 (((let _factorial := _wd_1_0;
  let _member : Litex.In _factorial Litex.C := Litex.naturalToComplex _factorial (Litex.factorialInN _factorial);
  (Litex.factorialDenoteNat _factorial 5 (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = ((5 : ℕ) : ℂ))))).trans (congrArg M.number (by norm_num)))).trans (congrArg M.number (by norm_num : (120 : ℂ) = ((120 : ℤ) : ℂ)))) rfl (by norm_num)))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (12 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.factorial (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (5 : ℂ)) ((5 : ℕ) : ℂ) Litex.N (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = ((5 : ℕ) : ℂ)))) (Litex.NativeBridge.numberInN (5))));
        let _wd_1_1 := (Litex.lcm (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (18 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) ((12 : ℤ) : ℂ) Litex.Z (((Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))).trans (congrArg M.number (by norm_num : (12 : ℂ) = ((12 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (12))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (18 : ℂ)) ((18 : ℤ) : ℂ) Litex.Z (((Litex.NativeBridge.denoteNumber (M := M) (18 : ℂ))).trans (congrArg M.number (by norm_num : (18 : ℂ) = ((18 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (18))));
        (Litex.gcd _wd_1_0 _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_0 ((120 : ℤ) : ℂ) Litex.Z (((let _factorial := _wd_1_0;
        let _member : Litex.In _factorial Litex.C := Litex.naturalToComplex _factorial (Litex.factorialInN _factorial);
        (Litex.factorialDenoteNat _factorial 5 (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = ((5 : ℕ) : ℂ))))).trans (congrArg M.number (by norm_num)))).trans (congrArg M.number (by norm_num : (120 : ℂ) = ((120 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (120))) (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 ((36 : ℤ) : ℂ) Litex.Z (((let _intop := _wd_1_1;
        let _member : Litex.In _intop Litex.C := Litex.naturalToComplex _intop (Litex.lcmInN _intop);
        (Litex.lcmDenoteInt _intop (12 : ℤ) (18 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))).trans (congrArg M.number (by norm_num : (12 : ℂ) = ((12 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (18 : ℂ))).trans (congrArg M.number (by norm_num : (18 : ℂ) = ((18 : ℤ) : ℂ))))).trans (congrArg M.number (by norm_num [Int.lcm_eq_natAbs_lcm_natAbs])))).trans (congrArg M.number (by norm_num : (36 : ℂ) = ((36 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (36))) (Or.inl (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_0 (Litex.number 0) ((120 : ℤ) : ℂ) 0 (((let _factorial := _wd_1_0;
        let _member : Litex.In _factorial Litex.C := Litex.naturalToComplex _factorial (Litex.factorialInN _factorial);
        (Litex.factorialDenoteNat _factorial 5 (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = ((5 : ℕ) : ℂ))))).trans (congrArg M.number (by norm_num)))).trans (congrArg M.number (by norm_num : (120 : ℂ) = ((120 : ℤ) : ℂ)))) rfl (by norm_num)))));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (12 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (12 : ℂ)) from (((let _intop := _equal_wd_1_0;
        let _member : Litex.In _intop Litex.C := Litex.naturalToComplex _intop (Litex.gcdInN _intop);
        (Litex.gcdDenoteInt _intop (120 : ℤ) (36 : ℤ) (((let _factorial := (_equal_wd_1_0).val.left;
        let _member : Litex.In _factorial Litex.C := Litex.naturalToComplex _factorial (Litex.factorialInN _factorial);
        (Litex.factorialDenoteNat _factorial 5 (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = ((5 : ℕ) : ℂ))))).trans (congrArg M.number (by norm_num)))).trans (congrArg M.number (by norm_num : (120 : ℂ) = ((120 : ℤ) : ℂ)))) (((let _intop := (_equal_wd_1_0).val.right;
        let _member : Litex.In _intop Litex.C := Litex.naturalToComplex _intop (Litex.lcmInN _intop);
        (Litex.lcmDenoteInt _intop (12 : ℤ) (18 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))).trans (congrArg M.number (by norm_num : (12 : ℂ) = ((12 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (18 : ℂ))).trans (congrArg M.number (by norm_num : (18 : ℂ) = ((18 : ℤ) : ℂ))))).trans (congrArg M.number (by norm_num [Int.lcm_eq_natAbs_lcm_natAbs])))).trans (congrArg M.number (by norm_num : (36 : ℂ) = ((36 : ℤ) : ℂ))))).trans (congrArg M.number (by norm_num [Int.gcd_eq_natAbs_gcd_natAbs])))).trans (congrArg M.number (by norm_num : (12 : ℂ) = (12 : ℂ)))).trans (((Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))).trans (congrArg M.number (by norm_num : (12 : ℂ) = (12 : ℂ)))).symm)))
      )
  )

theorem h_48 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (Litex.factorial (Litex.number (M := M) (5 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (5 : ℂ)) ((5 : ℕ) : ℂ) Litex.N (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = ((5 : ℕ) : ℂ)))) (Litex.NativeBridge.numberInN (5))));
  let _wd_1_1 := (Litex.lcm (Litex.number (M := M) (12 : ℂ)) (Litex.number (M := M) (18 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (12 : ℂ)) ((12 : ℤ) : ℂ) Litex.Z (((Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))).trans (congrArg M.number (by norm_num : (12 : ℂ) = ((12 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (12))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (18 : ℂ)) ((18 : ℤ) : ℂ) Litex.Z (((Litex.NativeBridge.denoteNumber (M := M) (18 : ℂ))).trans (congrArg M.number (by norm_num : (18 : ℂ) = ((18 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (18))));
  (Litex.gcd _wd_1_0 _wd_1_1 (Litex.NativeBridge.inOfDenoteNumber _wd_1_0 ((120 : ℤ) : ℂ) Litex.Z (((let _factorial := _wd_1_0;
  let _member : Litex.In _factorial Litex.C := Litex.naturalToComplex _factorial (Litex.factorialInN _factorial);
  (Litex.factorialDenoteNat _factorial 5 (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = ((5 : ℕ) : ℂ))))).trans (congrArg M.number (by norm_num)))).trans (congrArg M.number (by norm_num : (120 : ℂ) = ((120 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (120))) (Litex.NativeBridge.inOfDenoteNumber _wd_1_1 ((36 : ℤ) : ℂ) Litex.Z (((let _intop := _wd_1_1;
  let _member : Litex.In _intop Litex.C := Litex.naturalToComplex _intop (Litex.lcmInN _intop);
  (Litex.lcmDenoteInt _intop (12 : ℤ) (18 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (12 : ℂ))).trans (congrArg M.number (by norm_num : (12 : ℂ) = ((12 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (18 : ℂ))).trans (congrArg M.number (by norm_num : (18 : ℂ) = ((18 : ℤ) : ℂ))))).trans (congrArg M.number (by norm_num [Int.lcm_eq_natAbs_lcm_natAbs])))).trans (congrArg M.number (by norm_num : (36 : ℂ) = ((36 : ℤ) : ℂ)))) (Litex.NativeBridge.numberInZ (36))) (Or.inl (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_0 (Litex.number 0) ((120 : ℤ) : ℂ) 0 (((let _factorial := _wd_1_0;
  let _member : Litex.In _factorial Litex.C := Litex.naturalToComplex _factorial (Litex.factorialInN _factorial);
  (Litex.factorialDenoteNat _factorial 5 (((Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))).trans (congrArg M.number (by norm_num : (5 : ℂ) = ((5 : ℕ) : ℂ))))).trans (congrArg M.number (by norm_num)))).trans (congrArg M.number (by norm_num : (120 : ℂ) = ((120 : ℤ) : ℂ)))) rfl (by norm_num)))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (12 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_47 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_integer_x5f_operations_x2f_statement_x2e_lit
