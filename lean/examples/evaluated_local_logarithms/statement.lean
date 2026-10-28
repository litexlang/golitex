import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_local_x5f_logarithms_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

include M in
private theorem _sketch_1 : True := by
  have h_3 : (by
    let _equal_wd_1_0 := (Litex.log (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (8 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) Litex.R (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num))) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (8 : ℂ) Litex.R (show (M.number (8 : ℂ)) = M.number (8 : ℂ) from (congrArg M.number (show (8 : ℂ) = (8 : ℂ) from by norm_num))) (Litex.NativeBridge.numberInROfEq (8 : ℂ) (8 : ℝ) (by norm_num))) (Litex.NativeBridge.ltOfDenoteReal (Litex.number 0) (Litex.number (M := M) (2 : ℂ)) 0 (2 : ℝ) rfl (((show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num)))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (((2 : ℝ) : ℝ) : ℂ)))) (by norm_num)) (Litex.NativeBridge.ltOfDenoteReal (Litex.number 0) (Litex.number (M := M) (8 : ℂ)) 0 (8 : ℝ) rfl (((show (M.number (8 : ℂ)) = M.number (8 : ℂ) from (congrArg M.number (show (8 : ℂ) = (8 : ℂ) from by norm_num)))).trans (congrArg M.number (by norm_num : (8 : ℂ) = (((8 : ℝ) : ℝ) : ℂ)))) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number 1) (2 : ℂ) 1 (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num))) rfl (by norm_num)))
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
    (by
      litex_checked_step =>
        exact (
          (let _equal_wd_1_0 := (Litex.log (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (8 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) Litex.R (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num))) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (8 : ℂ) Litex.R (show (M.number (8 : ℂ)) = M.number (8 : ℂ) from (congrArg M.number (show (8 : ℂ) = (8 : ℂ) from by norm_num))) (Litex.NativeBridge.numberInROfEq (8 : ℂ) (8 : ℝ) (by norm_num))) (Litex.NativeBridge.ltOfDenoteReal (Litex.number 0) (Litex.number (M := M) (2 : ℂ)) 0 (2 : ℝ) rfl (((show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num)))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (((2 : ℝ) : ℝ) : ℂ)))) (by norm_num)) (Litex.NativeBridge.ltOfDenoteReal (Litex.number 0) (Litex.number (M := M) (8 : ℂ)) 0 (8 : ℝ) rfl (((show (M.number (8 : ℂ)) = M.number (8 : ℂ) from (congrArg M.number (show (8 : ℂ) = (8 : ℂ) from by norm_num)))).trans (congrArg M.number (by norm_num : (8 : ℂ) = (((8 : ℝ) : ℝ) : ℂ)))) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number 1) (2 : ℂ) 1 (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num))) rfl (by norm_num)));
          (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from (((let _exp_log := _equal_wd_1_0;
          let _member := Litex.realToComplex _exp_log (Litex.logInR _exp_log);
          (Litex.denoteLog _exp_log (2 : ℝ) (8 : ℝ) (by have _child : Litex.denote _exp_log.val.base = M.number (2 : ℂ) := (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)); have _cast : (2 : ℂ) = (((2 : ℝ) : ℝ) : ℂ) := (by norm_num); exact _child.trans (congrArg M.number _cast)) (by have _child : Litex.denote _exp_log.val.arg = M.number (8 : ℂ) := (Litex.NativeBridge.denoteNumber (M := M) (8 : ℂ)); have _cast : (8 : ℂ) = (((8 : ℝ) : ℝ) : ℂ) := (by norm_num); exact _child.trans (congrArg M.number _cast))).trans (congrArg M.number (by have _value : Real.log (8 : ℝ) / Real.log (2 : ℝ) = (3 : ℝ) := (by convert (Litex.rationalLogValue (2 : ℝ) (8 : ℝ) (3 : ℤ) (1 : ℕ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) using 1; norm_num); rw [_value]; norm_num : ((Real.log (8 : ℝ) / Real.log (2 : ℝ) : ℝ) : ℂ) = (3 : ℂ))))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))).trans (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))).symm)))
        )
    )
  have h_1 : (by
    let _equal_wd_1_0 := (Litex.log (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (8 : ℂ)) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) Litex.R (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num))) (Litex.NativeBridge.numberInROfEq (2 : ℂ) (2 : ℝ) (by norm_num))) (Litex.NativeBridge.inOfDenoteNumber (Litex.number (M := M) (8 : ℂ)) (8 : ℂ) Litex.R (show (M.number (8 : ℂ)) = M.number (8 : ℂ) from (congrArg M.number (show (8 : ℂ) = (8 : ℂ) from by norm_num))) (Litex.NativeBridge.numberInROfEq (8 : ℂ) (8 : ℝ) (by norm_num))) (Litex.NativeBridge.ltOfDenoteReal (Litex.number 0) (Litex.number (M := M) (2 : ℂ)) 0 (2 : ℝ) rfl (((show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num)))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (((2 : ℝ) : ℝ) : ℂ)))) (by norm_num)) (Litex.NativeBridge.ltOfDenoteReal (Litex.number 0) (Litex.number (M := M) (8 : ℂ)) 0 (8 : ℝ) rfl (((show (M.number (8 : ℂ)) = M.number (8 : ℂ) from (congrArg M.number (show (8 : ℂ) = (8 : ℂ) from by norm_num)))).trans (congrArg M.number (by norm_num : (8 : ℂ) = (((8 : ℝ) : ℝ) : ℂ)))) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number 1) (2 : ℂ) 1 (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num))) rfl (by norm_num)))
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
    (by
      litex_checked_step =>
        exact (
          h_3
        )
    )
  exact True.intro
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_local_x5f_logarithms_x2f_statement_x2e_lit
