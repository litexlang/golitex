import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_mathematical_x5f_constants_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_1 : Litex.In (Litex.number (M := M) ((Real.exp 1 : ℝ) : ℂ)) (Litex.RPos (M := M)) :=
  (by
    litex_complete =>
      exact (
        (show Litex.In (Litex.number (M := M) ((Real.exp 1 : ℝ) : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos (Real.exp 1) (Real.exp_pos 1))
      )
  )

theorem h_3 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((Real.exp 1 : ℝ) : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inRPos_positive (Litex.number (M := M) ((Real.exp 1 : ℝ) : ℂ)) (h_1 (M := M)))
      )
  )

theorem h_4 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) ((Real.exp 1 : ℝ) : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.ltToLe (Litex.number (M := M) 0) (Litex.number (M := M) ((Real.exp 1 : ℝ) : ℂ)) (h_3 (M := M)))
      )
  )

theorem h_5 : ¬ Litex.Same (Litex.number (M := M) ((Real.exp 1 : ℝ) : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) (Litex.number (M := M) ((Real.exp 1 : ℝ) : ℂ)) (h_3 (M := M))) _litex_zero.symm)
      )
  )

theorem h_6 : Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) :=
  (by
    litex_complete =>
      exact (
        (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)
      )
  )

theorem h_12 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inRPos_positive (Litex.number (M := M) (Real.pi : ℂ)) (h_6 (M := M)))
      )
  )

theorem h_13 : Litex.Le (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.ltToLe (Litex.number (M := M) 0) (Litex.number (M := M) (Real.pi : ℂ)) (h_12 (M := M)))
      )
  )

theorem h_14 : ¬ Litex.Same (Litex.number (M := M) (Real.pi : ℂ)) (Litex.number (M := M) (0 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) (Litex.number (M := M) (Real.pi : ℂ)) (h_12 (M := M))) _litex_zero.symm)
      )
  )

noncomputable def _object_w5 := (Litex.ln (Litex.number (M := M) ((Real.exp 1 : ℝ) : ℂ)) (h_1 (M := M)))

theorem h_15 : (by
  let _equal_wd_1_0 := (_object_w5 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w5 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)) from (Litex.lnEuler _equal_wd_1_0 rfl)))
      )
  )

noncomputable def _object_w7 := (Litex.exp (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)))

theorem h_27 : (by
  let _equal_wd_1_1 := (_object_w7 (M := M))
  exact Litex.Same (Litex.number (M := M) ((Real.exp 1 : ℝ) : ℂ)) _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_1 := (_object_w7 (M := M));
        (show Litex.Same (Litex.number (M := M) ((Real.exp 1 : ℝ) : ℂ)) _equal_wd_1_1 from (show Litex.Same _equal_wd_1_1 (Litex.number (M := M) ((Real.exp 1 : ℝ) : ℂ)) from Litex.denoteExp _equal_wd_1_1 1 rfl).symm))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_positive_x5f_mathematical_x5f_constants_x2f_statement_x2e_lit
