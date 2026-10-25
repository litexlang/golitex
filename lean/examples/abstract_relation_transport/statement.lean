import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_abstract_x5f_relation_x5f_transport_x2f_statement_x2e_lit

universe u v4 v5 v6 v7
variable {M : Litex.Semantics.{u}}

variable (abstract_prop_1 : (Fin 2 → M.Value) → Prop)

theorem h_5 (abstract_prop_1 : (Fin 2 → M.Value) → Prop) : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_18 : Litex.In _value_i4 (Litex.R (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_19 : Litex.In _value_i5 (Litex.R (M := M))) (h_1 : Litex.Same _value_i4 _value_i5) (h_2 : (abstract_prop_1 ![(Litex.denote _value_i4), (Litex.denote _value_i4)])), (((abstract_prop_1 ![(Litex.denote _value_i5), (Litex.denote _value_i4)])) ∧ ((abstract_prop_1 ![(Litex.denote _value_i5), (Litex.denote _value_i5)]))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_18 _Host_i5 _rep_i5 _value_i5 h_19 h_1 h_2
          have h_3 : (abstract_prop_1 ![(Litex.denote _value_i5), (Litex.denote _value_i4)]) :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (abstract_prop_1 ![_known_argument_0, _known_argument_1])) (Litex.denote _value_i5) (Litex.denote _value_i4)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (abstract_prop_1 ![_known_argument_0, _known_argument_1])) (Litex.denote _value_i4) (Litex.denote _value_i4)) := h_2
                    exact Eq.mp (((((Eq.refl ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (abstract_prop_1 ![_known_argument_0, _known_argument_1])) (Litex.denote _value_i4) (Litex.denote _value_i4)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (abstract_prop_1 ![_known_argument_0, _known_argument_1])) _known_value (Litex.denote _value_i4))) h_1))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (abstract_prop_1 ![_known_argument_0, _known_argument_1])) (Litex.denote _value_i5) _known_value)) (show @Eq M.Value _ _ from Eq.refl _))) _known_citation
                  )
                )
            )
          have h_4 : (abstract_prop_1 ![(Litex.denote _value_i5), (Litex.denote _value_i5)]) :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (abstract_prop_1 ![_known_argument_0, _known_argument_1])) (Litex.denote _value_i5) (Litex.denote _value_i5)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (abstract_prop_1 ![_known_argument_0, _known_argument_1])) (Litex.denote _value_i4) (Litex.denote _value_i4)) := h_2
                    exact Eq.mp (((((Eq.refl ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (abstract_prop_1 ![_known_argument_0, _known_argument_1])) (Litex.denote _value_i4) (Litex.denote _value_i4)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (abstract_prop_1 ![_known_argument_0, _known_argument_1])) _known_value (Litex.denote _value_i4))) h_1))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (abstract_prop_1 ![_known_argument_0, _known_argument_1])) (Litex.denote _value_i5) _known_value)) h_1)) _known_citation
                  )
                )
            )
          exact (And.intro h_3 h_4)
        )
      )
  )

theorem h_31 (abstract_prop_1 : (Fin 2 → M.Value) → Prop) : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_44 : Litex.In _value_i6 (Litex.R (M := M))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_45 : Litex.In _value_i7 (Litex.R (M := M))) (h_28 : Litex.Same _value_i6 _value_i7) (h_29 : ¬ ((abstract_prop_1 ![(Litex.denote _value_i6), (Litex.denote _value_i6)]))), ¬ ((abstract_prop_1 ![(Litex.denote _value_i7), (Litex.denote _value_i7)])) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_44 _Host_i7 _rep_i7 _value_i7 h_45 h_28 h_29
          have h_30 : ¬ ((abstract_prop_1 ![(Litex.denote _value_i7), (Litex.denote _value_i7)])) :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (¬ ((abstract_prop_1 ![_known_argument_0, _known_argument_1])))) (Litex.denote _value_i7) (Litex.denote _value_i7)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (¬ ((abstract_prop_1 ![_known_argument_0, _known_argument_1])))) (Litex.denote _value_i6) (Litex.denote _value_i6)) := h_29
                    exact Eq.mp (((((Eq.refl ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (¬ ((abstract_prop_1 ![_known_argument_0, _known_argument_1])))) (Litex.denote _value_i6) (Litex.denote _value_i6)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (¬ ((abstract_prop_1 ![_known_argument_0, _known_argument_1])))) _known_value (Litex.denote _value_i6))) h_28))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (¬ ((abstract_prop_1 ![_known_argument_0, _known_argument_1])))) (Litex.denote _value_i7) _known_value)) h_28)) _known_citation
                  )
                )
            )
          exact h_30
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_abstract_x5f_relation_x5f_transport_x2f_statement_x2e_lit
