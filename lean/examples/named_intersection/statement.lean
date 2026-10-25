import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_named_x5f_intersection_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

noncomputable def _object_i1 := (Litex.intersect (Litex.R (M := M)) (Litex.C (M := M)))
theorem h_3 : Litex.IsSet (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (Litex.intersect (Litex.R (M := M)) (Litex.C (M := M)))
          exact (Litex.isSet _atomic_wd_1_0))
      )
  )
theorem h_4 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (Litex.intersect (Litex.R (M := M)) (Litex.C (M := M))))
      )
  )

theorem h_5 : Litex.In (Litex.number (M := M) (1 : ℂ)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.inOfSame (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))) ((((Litex.sameRefl (_object_i1 (M := M)))).trans (h_4 (M := M)))).symm (by
          let _atomic_wd_2_1 := (_object_i1 (M := M))
          exact ((Litex.inIntersect_iff (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) (Litex.C (M := M))).mpr ⟨(Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num)), (Litex.numberInC (M := M) (1 : ℂ))⟩)))
      )
  )

theorem h_9 : (by
  let _atomic_wd_1_0 := (_object_i1 (M := M))
  exact Litex.IsSet _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_i1 (M := M))
          exact (Litex.isSetOfSame (_object_i1 (M := M)) _atomic_wd_1_0 (h_4 (M := M)) (h_3 (M := M))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_named_x5f_intersection_x2f_statement_x2e_lit
