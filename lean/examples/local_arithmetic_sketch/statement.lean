import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_local_x5f_arithmetic_x5f_sketch_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

include M in
private theorem _sketch_1 : True := by
  let _object_i1 := (Litex.number (M := M) (2 : ℂ))
  have h_2 : Litex.Same _object_i1 (Litex.number (M := M) (2 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.sameRefl (Litex.number (M := M) (2 : ℂ)))
        )
    )
  let _object_w2 := (Litex.add _object_i1 (Litex.number (M := M) (1 : ℂ)) (Litex.inOfSame (Litex.number (M := M) (2 : ℂ)) _object_i1 (Litex.C (M := M)) (Litex.C (M := M)) (h_2).symm (Litex.sameRefl (Litex.C (M := M))) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.numberInC (M := M) (1 : ℂ)))

  have h_1 : (by
    let _equal_wd_1_0 := _object_w2
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
    (by
      litex_checked_step =>
        exact (
          (((congrArg₂ M.addValue h_2 (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))))).trans (((let _equal_wd_2_0 := (Litex.add (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (3 : ℂ)) ((2 : ℂ) + (1 : ℂ)) (3 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num))))).trans ((Litex.sameRefl (Litex.number (M := M) (3 : ℂ)))).symm))
        )
    )
  exact True.intro

noncomputable def _object_i2 := (Litex.number (M := M) (5 : ℂ))
theorem h_455 : Litex.Same (_object_i2 (M := M)) (Litex.number (M := M) (5 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.number (M := M) (5 : ℂ)))
      )
  )

theorem h_456 : Litex.Same (_object_i2 (M := M)) (Litex.number (M := M) (5 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (h_455 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_local_x5f_arithmetic_x5f_sketch_x2f_statement_x2e_lit
