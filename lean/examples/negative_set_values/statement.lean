import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_negative_x5f_set_x5f_values_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

noncomputable def _object_w1 := (let _setTail_0 := Litex.emptySet (M := M);
  _setTail_0)

theorem h_1 : (by
  let _atomic_wd_1_0 := (_object_w1 (M := M))
  exact ¬ Litex.IsNonempty _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          let _atomic_wd_1_0 := (_object_w1 (M := M))
          exact (Litex.emptyNotNonempty (M := M)))
      )
  )

theorem h_2 : ¬ Litex.IsFiniteSet (Litex.N (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.naturalNotFinite (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_negative_x5f_set_x5f_values_x2f_statement_x2e_lit
