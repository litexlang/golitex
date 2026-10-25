import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_arbitrary_x5f_carrier_x5f_pairs_x2f_statement_x2e_lit

universe u v1 v2 v3 v6 v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

variable {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1)

theorem _struct_field_checks_2 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) : ∀ {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_2 : Litex.In _value_i2 _value_i1) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_3 : Litex.In _value_i3 _value_i1), True := by
  intro _Host_i2 _rep_i2 _value_i2 h_2 _Host_i3 _rep_i3 _value_i3 h_3
  exact True.intro

noncomputable def struct_2 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) : Litex.Obj (M := M) (Litex.CartObj M 2) :=
  Litex.cart (M := M) ![Litex.denote _value_i1, Litex.denote _value_i1] (by
  have _finiteProof_0 := (Litex.isSet _value_i1)
  have _finiteProof_1 := (Litex.isSet _value_i1)
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)

theorem h_5 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_1 : Litex.IsSet _value_i1) : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_18 : Litex.In _value_i6 _value_i1) {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_19 : Litex.In _value_i7 _value_i1), (by
  let _object_w1 := (Litex.tuple (M := M) ![Litex.denote _value_i6, Litex.denote _value_i7] (Fin.cases (Litex.isSet _value_i6) (Fin.cases (Litex.isSet _value_i7) (fun i => Fin.elim0 i))))
  let _object_w2 := (struct_2 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1)
  exact (by
    let _atomic_wd_1_0 := _object_w1
    let _atomic_wd_1_1 := _object_w2
    exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_18 _Host_i7 _rep_i7 _value_i7 h_19
          let _object_w1 := (Litex.tuple (M := M) ![Litex.denote _value_i6, Litex.denote _value_i7] (Fin.cases (Litex.isSet _value_i6) (Fin.cases (Litex.isSet _value_i7) (fun i => Fin.elim0 i))))
          let _object_w2 := (struct_2 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1)
          have h_4 : (by
            let _atomic_wd_1_0 := _object_w1
            let _atomic_wd_1_1 := _object_w2
            exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w1
                    let _atomic_wd_1_1 := _object_w2
                    exact (Litex.tupleInCart _atomic_wd_1_0 (struct_2 (M := M) (_Host_i1 := _Host_i1) (_rep_i1 := _rep_i1) _value_i1 h_1) (by
                      have _finiteProof_0 := (h_18)
                      have _finiteProof_1 := (h_19)
                      exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                    )))
                )
            )
          exact h_4
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_arbitrary_x5f_carrier_x5f_pairs_x2f_statement_x2e_lit
