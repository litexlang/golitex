import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_local_x5f_facts_x2f_statement_x2e_lit

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
  have h_404 : (by
    let _equal_wd_1_0 := (Litex.add _object_i1 (Litex.number (M := M) (1 : ℂ)) (Litex.inOfSame (Litex.number (M := M) (2 : ℂ)) _object_i1 (Litex.C (M := M)) (Litex.C (M := M)) (h_2).symm (Litex.sameRefl (Litex.C (M := M))) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
    (by
      litex_checked_step =>
        exact (
          (let _equal_wd_1_0 := (Litex.add _object_i1 (Litex.number (M := M) (1 : ℂ)) (Litex.inOfSame (Litex.number (M := M) (2 : ℂ)) _object_i1 (Litex.C (M := M)) (Litex.C (M := M)) (h_2).symm (Litex.sameRefl (Litex.C (M := M))) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.numberInC (M := M) (1 : ℂ)));
          (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from ((congrArg₂ M.addValue h_2 (Eq.refl (M.number (1 : ℂ))))).trans (((show (M.addValue (M.number (2 : ℂ)) (M.number (1 : ℂ))) = M.number (3 : ℂ) from ((congrArg₂ M.addValue (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num))) (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num)))).trans ((M.add_numbers (2 : ℂ) (1 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans ((show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).symm))))
        )
    )
  have h_1 : (by
    let _equal_wd_1_0 := (Litex.add _object_i1 (Litex.number (M := M) (1 : ℂ)) (Litex.inOfSame (Litex.number (M := M) (2 : ℂ)) _object_i1 (Litex.C (M := M)) (Litex.C (M := M)) (h_2).symm (Litex.sameRefl (Litex.C (M := M))) (Litex.numberInC (M := M) (2 : ℂ))) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
    (by
      litex_checked_step =>
        exact (
          h_404
        )
    )
  exact True.intro

noncomputable def _object_i2 := (Litex.number (M := M) (5 : ℂ))
theorem h_807 : Litex.Same (_object_i2 (M := M)) (Litex.number (M := M) (5 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.number (M := M) (5 : ℂ)))
      )
  )

theorem h_1209 : (by
  let _equal_wd_1_0 := (Litex.add (_object_i2 (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.inOfSame (Litex.number (M := M) (5 : ℂ)) (_object_i2 (M := M)) (Litex.C (M := M)) (Litex.C (M := M)) ((h_807 (M := M))).symm (Litex.sameRefl (Litex.C (M := M))) (Litex.numberInC (M := M) (5 : ℂ))) (Litex.numberInC (M := M) (1 : ℂ)))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (Litex.add (_object_i2 (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.inOfSame (Litex.number (M := M) (5 : ℂ)) (_object_i2 (M := M)) (Litex.C (M := M)) (Litex.C (M := M)) ((h_807 (M := M))).symm (Litex.sameRefl (Litex.C (M := M))) (Litex.numberInC (M := M) (5 : ℂ))) (Litex.numberInC (M := M) (1 : ℂ)));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) from ((congrArg₂ M.addValue (h_807 (M := M)) (Eq.refl (M.number (1 : ℂ))))).trans (((show (M.addValue (M.number (5 : ℂ)) (M.number (1 : ℂ))) = M.number (6 : ℂ) from ((congrArg₂ M.addValue (show (M.number (5 : ℂ)) = M.number (5 : ℂ) from (congrArg M.number (show (5 : ℂ) = (5 : ℂ) from by norm_num))) (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num)))).trans ((M.add_numbers (5 : ℂ) (1 : ℂ)).trans (congrArg M.number (by norm_num)))))).trans ((show (M.number (6 : ℂ)) = M.number (6 : ℂ) from (congrArg M.number (show (6 : ℂ) = (6 : ℂ) from by norm_num)))).symm))))
      )
  )

theorem h_1611 : (by
  let _equal_wd_1_0 := (Litex.add (_object_i2 (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.inOfSame (Litex.number (M := M) (5 : ℂ)) (_object_i2 (M := M)) (Litex.C (M := M)) (Litex.C (M := M)) ((h_807 (M := M))).symm (Litex.sameRefl (Litex.C (M := M))) (Litex.numberInC (M := M) (5 : ℂ))) (Litex.numberInC (M := M) (1 : ℂ)))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_1209 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_local_x5f_facts_x2f_statement_x2e_lit
