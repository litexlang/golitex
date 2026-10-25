import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_abstract_x5f_proposition_x5f_identity_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}

variable (abstract_prop_1 : (Fin 0 → M.Value) → Prop)

theorem h_3 (abstract_prop_1 : (Fin 0 → M.Value) → Prop) : ∀ (h_1 : (abstract_prop_1 (fun i : Fin 0 => Fin.elim0 i))), (abstract_prop_1 (fun i : Fin 0 => Fin.elim0 i)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro h_1
          have h_2 : (abstract_prop_1 (fun i : Fin 0 => Fin.elim0 i)) :=
            (by
              litex_checked_step =>
                exact (
                  h_1
                )
            )
          exact h_2
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_abstract_x5f_proposition_x5f_identity_x2f_statement_x2e_lit
