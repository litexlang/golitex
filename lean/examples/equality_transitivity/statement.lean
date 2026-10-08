import Litex

namespace LitexCompiled.file_lean_x2f_examples_x2f_equality_x5f_transitivity_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6 v7
variable {M : Litex.Semantics.{u}}

theorem fact_1 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (_h_param_i1 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (_h_param_i2 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (_h_param_i3 : Litex.In _value_i3 (Litex.R (M := M))) (_h_dom_f1 : Litex.Same _value_i1 _value_i2) (_h_dom_f2 : Litex.Same _value_i2 _value_i3), (Litex.Same _value_i1 _value_i3 ∧ (Litex.Same _value_i3 _value_i1 ∧ Litex.Same (Litex.add _value_i1 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i1 _h_param_i1) (Litex.numberInC (M := M) (1 : ℂ))) (Litex.add _value_i3 (Litex.number (M := M) (1 : ℂ)) (Litex.realToComplex _value_i3 (Litex.inOfSame _value_i1 _value_i3 (Litex.R (M := M)) (Litex.R (M := M)) (((Litex.sameRefl _value_i1)).trans (((((Litex.sameRefl _value_i1)).trans _h_dom_f1)).trans _h_dom_f2)) (Litex.sameRefl (Litex.R (M := M))) _h_param_i1)) (Litex.numberInC (M := M) (1 : ℂ))))) :=
  (by
    intro _Host_i1 _rep_i1 _value_i1 _h_param_i1 _Host_i2 _rep_i2 _value_i2 _h_param_i2 _Host_i3 _rep_i3 _value_i3 _h_param_i3 _h_dom_f1 _h_dom_f2
    exact (And.intro (((((Litex.sameRefl _value_i1)).trans _h_dom_f1)).trans _h_dom_f2) (And.intro (((Litex.sameRefl _value_i3)).trans ((((((Litex.sameRefl _value_i1)).trans _h_dom_f1)).trans _h_dom_f2)).symm) (congrArg₂ M.addValue (((Litex.sameRefl _value_i1)).trans (((((Litex.sameRefl _value_i1)).trans _h_dom_f1)).trans _h_dom_f2)) (Litex.sameRefl (Litex.number (M := M) (1 : ℂ))))))
  )

theorem fact_2 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (_h_param_i4 : Litex.In _value_i4 (Litex.R (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (_h_param_i5 : Litex.In _value_i5 (Litex.R (M := M))) (_h_dom_f87 : Litex.Same _value_i4 _value_i5), Litex.Same _value_i5 _value_i4 :=
  (by
    intro _Host_i4 _rep_i4 _value_i4 _h_param_i4 _Host_i5 _rep_i5 _value_i5 _h_param_i5 _h_dom_f87
    exact (((Litex.sameRefl _value_i5)).trans (_h_dom_f87).symm)
  )

theorem fact_3 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (_h_param_i6 : Litex.In _value_i6 (Litex.R (M := M))) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (_h_param_i7 : Litex.In _value_i7 (Litex.R (M := M))) (_h_dom_f105 : Litex.Same _value_i6 _value_i7), Litex.Same _value_i7 _value_i6 :=
  (by
    intro _Host_i6 _rep_i6 _value_i6 _h_param_i6 _Host_i7 _rep_i7 _value_i7 _h_param_i7 _h_dom_f105
    exact ((fact_2 (M := M)) _value_i6 _h_param_i6 _value_i7 _h_param_i7 _h_dom_f105)
  )
end LitexCompiled.file_lean_x2f_examples_x2f_equality_x5f_transitivity_x2f_statement_x2e_lit
