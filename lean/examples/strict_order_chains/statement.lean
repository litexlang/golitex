import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_strict_x5f_order_x5f_chains_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6 v7 v8 v9
variable {M : Litex.Semantics.{u}}

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_17 : Litex.In _value_i1 (Litex.R (M := M))) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_18 : Litex.In _value_i2 (Litex.R (M := M))) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_19 : Litex.In _value_i3 (Litex.R (M := M))) (h_1 : Litex.Lt _value_i1 _value_i2) (h_2 : Litex.Lt _value_i2 _value_i3), Litex.Lt _value_i1 _value_i3 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_17 _Host_i2 _rep_i2 _value_i2 h_18 _Host_i3 _rep_i3 _value_i3 h_19 h_1 h_2
          have h_3 : Litex.Lt _value_i1 _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltTrans _value_i1 _value_i2 _value_i3 h_1 h_2)
                )
            )
          exact h_3
        )
      )
  )

theorem h_121 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_136 : Litex.In _value_i4 (Litex.R (M := M))) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_137 : Litex.In _value_i5 (Litex.R (M := M))) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_138 : Litex.In _value_i6 (Litex.R (M := M))) (h_118 : Litex.Lt _value_i4 _value_i5) (h_119 : Litex.Le _value_i5 _value_i6), Litex.Lt _value_i4 _value_i6 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_136 _Host_i5 _rep_i5 _value_i5 h_137 _Host_i6 _rep_i6 _value_i6 h_138 h_118 h_119
          have h_120 : Litex.Lt _value_i4 _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltLeTrans _value_i4 _value_i5 _value_i6 h_118 h_119)
                )
            )
          exact h_120
        )
      )
  )

theorem h_274 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_289 : Litex.In _value_i7 (Litex.R (M := M))) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_290 : Litex.In _value_i8 (Litex.R (M := M))) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_291 : Litex.In _value_i9 (Litex.R (M := M))) (h_271 : Litex.Le _value_i7 _value_i8) (h_272 : Litex.Lt _value_i8 _value_i9), Litex.Lt _value_i7 _value_i9 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_289 _Host_i8 _rep_i8 _value_i8 h_290 _Host_i9 _rep_i9 _value_i9 h_291 h_271 h_272
          have h_273 : Litex.Lt _value_i7 _value_i9 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.leLtTrans _value_i7 _value_i8 _value_i9 h_271 h_272)
                )
            )
          exact h_273
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_strict_x5f_order_x5f_chains_x2f_statement_x2e_lit
