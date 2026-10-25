import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_interval_x5f_bounds_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6 v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_20 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_21 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_34 : Litex.In _value_i3 (Litex.realInterval false true _value_i1 _value_i2 h_20 h_21)), ((Litex.In _value_i3 (Litex.R (M := M))) ∧ (((Litex.Lt _value_i1 _value_i3) ∧ (Litex.Le _value_i3 _value_i2)))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_20 _Host_i2 _rep_i2 _value_i2 h_21 _Host_i3 _rep_i3 _value_i3 h_34
          have h_35 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.inRealInterval_iff (Litex.realInterval false true _value_i1 _value_i2 h_20 h_21) _value_i3).mp h_34).1
                )
            )
          have h_36 : Litex.Lt _value_i1 _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.inRealInterval_iff (Litex.realInterval false true _value_i1 _value_i2 h_20 h_21) _value_i3).mp h_34).2.1
                )
            )
          have h_37 : Litex.Le _value_i3 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.inRealInterval_iff (Litex.realInterval false true _value_i1 _value_i2 h_20 h_21) _value_i3).mp h_34).2.2
                )
            )
          have h_1 : Litex.In _value_i3 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_35
                )
            )
          have h_2 : Litex.Lt _value_i1 _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  h_36
                )
            )
          have h_3 : Litex.Le _value_i3 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  h_37
                )
            )
          exact (And.intro h_1 (And.intro h_2 h_3))
        )
      )
  )

theorem h_151 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_166 : Litex.In _value_i4 (Litex.R (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_172 : Litex.In _value_i5 (Litex.realRay true true _value_i4 h_166)), ((Litex.In _value_i5 (Litex.R (M := M))) ∧ (Litex.Le _value_i4 _value_i5)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_166 _Host_i5 _rep_i5 _value_i5 h_172
          have h_173 : Litex.In _value_i5 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.inRealRay_iff (Litex.realRay true true _value_i4 h_166) _value_i5).mp h_172).1
                )
            )
          have h_174 : Litex.Le _value_i4 _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.inRealRay_iff (Litex.realRay true true _value_i4 h_166) _value_i5).mp h_172).2
                )
            )
          have h_149 : Litex.In _value_i5 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_173
                )
            )
          have h_150 : Litex.Le _value_i4 _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  h_174
                )
            )
          exact (And.intro h_149 h_150)
        )
      )
  )

theorem h_277 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_292 : Litex.In _value_i6 (Litex.R (M := M))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_298 : Litex.In _value_i7 (Litex.realRay false false _value_i6 h_292)), ((Litex.In _value_i7 (Litex.R (M := M))) ∧ (Litex.Lt _value_i7 _value_i6)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_292 _Host_i7 _rep_i7 _value_i7 h_298
          have h_299 : Litex.In _value_i7 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.inRealRay_iff (Litex.realRay false false _value_i6 h_292) _value_i7).mp h_298).1
                )
            )
          have h_300 : Litex.Lt _value_i7 _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  ((Litex.inRealRay_iff (Litex.realRay false false _value_i6 h_292) _value_i7).mp h_298).2
                )
            )
          have h_275 : Litex.In _value_i7 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_299
                )
            )
          have h_276 : Litex.Lt _value_i7 _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  h_300
                )
            )
          exact (And.intro h_275 h_276)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_real_x5f_interval_x5f_bounds_x2f_statement_x2e_lit
