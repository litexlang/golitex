import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_local_x5f_integer_x5f_operations_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

include M in
private theorem _sketch_1 : True := by
  let _object_i1 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)))
  have h_6 : Litex.In _object_i1 (Litex.Z (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (7 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (7 : ℂ)) (-7 : ℤ) (by norm_num))))
        )
    )
  have h_7 : Litex.Same _object_i1 _object_i1 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.sameRefl (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ))))
        )
    )
  have h_17 : (by
    let _equal_wd_1_0 := (Litex.mod _object_i1 (Litex.number (M := M) (3 : ℂ)) h_6 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
    (by
      litex_checked_step =>
        exact (
          (let _equal_wd_1_0 := (Litex.mod _object_i1 (Litex.number (M := M) (3 : ℂ)) h_6 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = ((Litex.integerDivisionValue (M := M) false) (Litex.denote _object_i1) (M.number (3 : ℂ))) from congrArg₂ (Litex.integerDivisionValue (M := M) false) (show Litex.denote _object_i1 = (Litex.denote _object_i1) from rfl) (show Litex.denote (Litex.number (M := M) (3 : ℂ)) = (M.number (3 : ℂ)) from rfl)) (((congrArg₂ (Litex.integerDivisionValue (M := M) false) (Eq.trans (Eq.trans (Eq.symm (show Litex.denote _object_i1 = (Litex.denote _object_i1) from rfl)) h_7) (show Litex.denote _object_i1 = (M.negValue (M.number (7 : ℂ))) from Eq.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)))).trans (congrArg M.number (by norm_num : (- (7 : ℂ)) = (-7 : ℂ)))) (Eq.symm (show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num)))))))) (Eq.refl (M.number (3 : ℂ))))).trans (show ((Litex.integerDivisionValue (M := M) false) (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ))) = M.number (2 : ℂ) from (congrArg₂ (Litex.integerDivisionValue (M := M) false) (show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num))))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans (by
            have _numeric := Litex.integerDivisionValue_numbers false (M := M) (-7 : ℤ) (3 : ℤ)
            norm_num [Int.gcd_eq_natAbs_gcd_natAbs, Int.lcm_eq_natAbs_lcm_natAbs] at _numeric
            exact _numeric))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))).symm)))
        )
    )
  have h_1 : (by
    let _equal_wd_1_0 := (Litex.mod _object_i1 (Litex.number (M := M) (3 : ℂ)) h_6 (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
    (by
      litex_checked_step =>
        exact (
          h_17
        )
    )
  exact True.intro
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_local_x5f_integer_x5f_operations_x2f_statement_x2e_lit
