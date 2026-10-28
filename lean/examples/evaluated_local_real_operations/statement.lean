import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_local_x5f_real_x5f_operations_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

include M in
private theorem _sketch_1 : True := by
  let _object_i1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)));
  let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
  (Litex.div _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-5 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (5 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)))).trans (congrArg M.number (by norm_num : (- (5 : ℂ)) = (-5 : ℂ)))) (Litex.numberInC (M := M) (-5 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
  have h_14 : Litex.In _object_i1 (Litex.R (M := M)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)));
            let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
            (Litex.div _wd_1_0 _wd_1_1 (by
              let _atomic_wd_2_0 := _wd_1_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (-5 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (5 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)))).trans (congrArg M.number (by norm_num : (- (5 : ℂ)) = (-5 : ℂ)))) (Litex.numberInC (M := M) (-5 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((- (5 : ℂ)) / (4 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (_atomic_wd_1_0).val.left (Litex.number (M := M) (4 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (5 : ℂ)) ((_atomic_wd_1_0).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ))) (Litex.NativeBridge.numberInROfEq ((- (5 : ℂ)) / (4 : ℂ)) ((-5 : ℝ) / (4 : ℝ)) (by norm_num))))
        )
    )
  have h_15 : Litex.Same _object_i1 _object_i1 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.sameRefl (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)));
          let _wd_1_1 := (Litex.number (M := M) (4 : ℂ));
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-5 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (5 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)))).trans (congrArg M.number (by norm_num : (- (5 : ℂ)) = (-5 : ℂ)))) (Litex.numberInC (M := M) (-5 : ℂ)))) (Litex.numberInC (M := M) (4 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (4 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (4 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))))
        )
    )
  have h_21 : (by
    let _equal_wd_1_0 := (Litex.ceil _object_i1 h_14)
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (-1 : ℂ))) :=
    (by
      litex_checked_step =>
        exact (
          (let _equal_wd_1_0 := (Litex.ceil _object_i1 h_14);
          (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (-1 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (-1 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = ((Litex.roundingValue (M := M) true) (Litex.denote _object_i1)) from congrArg (Litex.roundingValue (M := M) true) (show Litex.denote _object_i1 = (Litex.denote _object_i1) from rfl)) (((congrArg (Litex.roundingValue (M := M) true) (Eq.trans (Eq.trans (Eq.symm (show Litex.denote _object_i1 = (Litex.denote _object_i1) from rfl)) h_15) (show Litex.denote _object_i1 = (M.divValue (M.negValue (M.number (5 : ℂ))) (M.number (4 : ℂ))) from congrArg₂ M.divValue (show Litex.denote (_object_i1).val.left = (M.negValue (M.number (5 : ℂ))) from Eq.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)))).trans (congrArg M.number (by norm_num : (- (5 : ℂ)) = (-5 : ℂ)))) (Eq.symm (show (M.negValue (M.number (5 : ℂ))) = M.number (-5 : ℂ) from ((congrArg M.negValue (show (M.number (5 : ℂ)) = M.number (5 : ℂ) from (congrArg M.number (show (5 : ℂ) = (5 : ℂ) from by norm_num)))).trans ((M.neg_numbers (5 : ℂ)).trans (congrArg M.number (by norm_num))))))) (show Litex.denote (Litex.number (M := M) (4 : ℂ)) = (M.number (4 : ℂ)) from rfl))))).trans (show ((Litex.roundingValue (M := M) true) (M.divValue (M.negValue (M.number (5 : ℂ))) (M.number (4 : ℂ)))) = M.number (-1 : ℂ) from (congrArg (Litex.roundingValue (M := M) true) (show (M.divValue (M.negValue (M.number (5 : ℂ))) (M.number (4 : ℂ))) = M.number ((-5 : ℂ) / (4 : ℂ)) from ((congrArg₂ M.divValue (show (M.negValue (M.number (5 : ℂ))) = M.number (-5 : ℂ) from ((congrArg M.negValue (show (M.number (5 : ℂ)) = M.number (5 : ℂ) from (congrArg M.number (show (5 : ℂ) = (5 : ℂ) from by norm_num)))).trans ((M.neg_numbers (5 : ℂ)).trans (congrArg M.number (by norm_num))))) (show (M.number (4 : ℂ)) = M.number (4 : ℂ) from (congrArg M.number (show (4 : ℂ) = (4 : ℂ) from by norm_num)))).trans ((M.div_numbers (-5 : ℂ) (4 : ℂ) (by norm_num)).trans (congrArg M.number (by norm_num)))))).trans (by
            have _numeric := Litex.roundingValue_number true (M := M) ((-5 : ℝ) / (4 : ℝ))
            norm_num [Real.sign] at _numeric
            simpa only [neg_div] using _numeric))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))).trans (congrArg M.number (by norm_num : (-1 : ℂ) = (-1 : ℂ)))).symm)))
        )
    )
  have h_1 : (by
    let _equal_wd_1_0 := (Litex.ceil _object_i1 h_14)
    let _equal_wd_1_1 := (Litex.number (M := M) (-1 : ℂ))
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          h_21
        )
    )
  exact True.intro
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_local_x5f_real_x5f_operations_x2f_statement_x2e_lit
