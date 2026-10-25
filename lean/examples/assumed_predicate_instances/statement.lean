import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_assumed_x5f_predicate_x5f_instances_x2f_statement_x2e_lit

universe u v3
variable {M : Litex.Semantics.{u}}

variable (abstract_prop_1 : (Fin 1 → M.Value) → Prop)

variable (h_2 : ∀ (_value_i3 : Litex.Obj (M := M) M.Value) (h_3 : Litex.In _value_i3 (Litex.R (M := M))), (abstract_prop_1 ![(Litex.denote _value_i3)]))

theorem h_5 (abstract_prop_1 : (Fin 1 → M.Value) → Prop) (h_2 : ∀ (_value_i3 : Litex.Obj (M := M) M.Value) (h_3 : Litex.In _value_i3 (Litex.R (M := M))), (abstract_prop_1 ![(Litex.denote _value_i3)])) : (abstract_prop_1 ![(Litex.denote (Litex.number (M := M) (0 : ℂ)))]) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_6 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) :=
            (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
          exact ((show ∀ {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_3 : Litex.In _value_i3 (Litex.R (M := M))), (abstract_prop_1 ![(Litex.denote _value_i3)]) from (fun {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_3 : Litex.In _value_i3 (Litex.R (M := M))) => by
          exact h_2 (Litex.semanticObject (Litex.denote _value_i3) (Litex.isSet _value_i3)) h_3)) (Litex.number (M := M) (0 : ℂ)) h_6)
        )
      )
  )

theorem h_8 (abstract_prop_1 : (Fin 1 → M.Value) → Prop) (h_2 : ∀ (_value_i3 : Litex.Obj (M := M) M.Value) (h_3 : Litex.In _value_i3 (Litex.R (M := M))), (abstract_prop_1 ![(Litex.denote _value_i3)])) : (abstract_prop_1 ![(Litex.denote (Litex.number (M := M) (0 : ℂ)))]) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_7 : Litex.In (Litex.number (M := M) (0 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (0 : ℂ) (0 : ℝ) (by norm_num))
                )
            )
          exact ((show ∀ {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_3 : Litex.In _value_i3 (Litex.R (M := M))), (abstract_prop_1 ![(Litex.denote _value_i3)]) from (fun {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_3 : Litex.In _value_i3 (Litex.R (M := M))) => by
          exact h_2 (Litex.semanticObject (Litex.denote _value_i3) (Litex.isSet _value_i3)) h_3)) (Litex.number (M := M) (0 : ℂ)) h_7)
        )
      )
  )

theorem h_11 (abstract_prop_1 : (Fin 1 → M.Value) → Prop) (h_2 : ∀ (_value_i3 : Litex.Obj (M := M) M.Value) (h_3 : Litex.In _value_i3 (Litex.R (M := M))), (abstract_prop_1 ![(Litex.denote _value_i3)])) : (abstract_prop_1 ![(Litex.denote (Litex.number (M := M) (1 : ℂ)))]) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_12 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
                )
            )
          have h_13 : (abstract_prop_1 ![(Litex.denote (Litex.number (M := M) (1 : ℂ)))]) :=
            (by
              litex_checked_step =>
                exact (
                  ((show ∀ {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_3 : Litex.In _value_i3 (Litex.R (M := M))), (abstract_prop_1 ![(Litex.denote _value_i3)]) from (fun {_Host_i3 : Type _} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_3 : Litex.In _value_i3 (Litex.R (M := M))) => by
                    exact h_2 (Litex.semanticObject (Litex.denote _value_i3) (Litex.isSet _value_i3)) h_3)) (Litex.number (M := M) (1 : ℂ)) h_12)
                )
            )
          exact h_13
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_assumed_x5f_predicate_x5f_instances_x2f_statement_x2e_lit
