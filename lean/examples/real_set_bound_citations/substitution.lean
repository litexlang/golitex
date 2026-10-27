import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_set_x5f_bound_x5f_citations_x2f_substitution_x2e_lit

universe u v1 v2 v3 v4
variable {M : Litex.Semantics.{u}}

theorem h_7 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_20 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_21 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_22 : Litex.In _value_i3 (Litex.R (M := M))) {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_23 : Litex.In _value_i4 (Litex.R (M := M))) (h_1 : Litex.Subset _value_i1 (Litex.R (M := M))) (h_2 : Litex.Subset _value_i2 (Litex.R (M := M))) (h_3 : Litex.Same _value_i1 _value_i2) (h_4 : Litex.Same _value_i3 _value_i4) (h_5 : Litex.RealUpperBound _value_i1 _value_i3), Litex.RealUpperBound _value_i2 _value_i4 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_20 _Host_i2 _rep_i2 _value_i2 h_21 _Host_i3 _rep_i3 _value_i3 h_22 _Host_i4 _rep_i4 _value_i4 h_23 h_1 h_2 h_3 h_4 h_5
          have h_42 : ∀ {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i7 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i7 _value_i1), (∃ (_r _s : ℝ), (Litex.denote _value_i7) = M.number (_r : ℂ) ∧ (Litex.denote _value_i3) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i7 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i7 _value_i1) => (h_5) (Litex.denote _value_i7) _member)
                )
            )
          have h_6 : Litex.RealUpperBound _value_i2 _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealUpperBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _value_i2) (Litex.denote _value_i4)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealUpperBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _value_i1) (Litex.denote _value_i3)) := h_5
                    exact Eq.mp (((((Eq.refl ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealUpperBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _value_i1) (Litex.denote _value_i3)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealUpperBoundValue M _known_argument_0 _known_argument_1)) _known_value (Litex.denote _value_i3))) h_3))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (Litex.RealUpperBoundValue M _known_argument_0 _known_argument_1)) (Litex.denote _value_i2) _known_value)) h_4)) _known_citation
                  )
                )
            )
          have h_48 : ∀ {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i8 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i8 _value_i2), (∃ (_r _s : ℝ), (Litex.denote _value_i8) = M.number (_r : ℂ) ∧ (Litex.denote _value_i4) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
            (by
              litex_checked_step =>
                exact (
                  (fun {_Host : Type _} [_rep : Litex.Representation M _Host] (_value_i8 : Litex.Obj (M := M) _Host) (_member : Litex.In _value_i8 _value_i2) => (h_6) (Litex.denote _value_i8) _member)
                )
            )
          exact h_6
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_set_x5f_bound_x5f_citations_x2f_substitution_x2e_lit
