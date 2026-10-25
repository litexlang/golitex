import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_intersection_x5f_membership_x2f_statement_x2e_lit

universe u v1 v2 v3 v4 v5 v6
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_setSemantics : Litex.SetSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_17 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_18 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_19 : Litex.In _value_i3 (Litex.R (M := M))) (h_1 : Litex.In _value_i3 _value_i1) (h_2 : Litex.In _value_i3 _value_i2), (by
  let _object_w2 := (Litex.intersect _value_i1 _value_i2)
  exact (by
    let _atomic_wd_1_1 := _object_w2
    exact Litex.In _value_i3 _atomic_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_17 _Host_i2 _rep_i2 _value_i2 h_18 _Host_i3 _rep_i3 _value_i3 h_19 h_1 h_2
          let _object_w2 := (Litex.intersect _value_i1 _value_i2)
          have h_3 : (by
            let _atomic_wd_1_1 := _object_w2
            exact Litex.In _value_i3 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := _object_w2
                    exact ((Litex.inIntersect_iff _value_i3 _value_i1 _value_i2).mpr ⟨h_1, h_2⟩))
                )
            )
          have h_72 : Litex.In _value_i3 _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  (((Litex.inIntersect_iff _value_i3 _value_i1 _value_i2).mp h_3).1)
                )
            )
          have h_73 : Litex.In _value_i3 _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  (((Litex.inIntersect_iff _value_i3 _value_i1 _value_i2).mp h_3).2)
                )
            )
          exact h_3
        )
      )
  )

theorem h_76 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_78 : Litex.IsSet _value_i4) {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_79 : Litex.IsSet _value_i5) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_80 : Litex.In _value_i6 (Litex.intersect _value_i4 _value_i5)), ((Litex.In _value_i6 _value_i4) ∧ (Litex.In _value_i6 _value_i5)) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_78 _Host_i5 _rep_i5 _value_i5 h_79 _Host_i6 _rep_i6 _value_i6 h_80
          have h_81 : Litex.In _value_i6 _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  (((Litex.inIntersect_iff _value_i6 _value_i4 _value_i5).mp h_80).1)
                )
            )
          have h_82 : Litex.In _value_i6 _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  (((Litex.inIntersect_iff _value_i6 _value_i4 _value_i5).mp h_80).2)
                )
            )
          have h_74 : Litex.In _value_i6 _value_i4 :=
            (by
              litex_checked_step =>
                exact (
                  h_81
                )
            )
          have h_75 : Litex.In _value_i6 _value_i5 :=
            (by
              litex_checked_step =>
                exact (
                  h_82
                )
            )
          exact (And.intro h_74 h_75)
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_intersection_x5f_membership_x2f_statement_x2e_lit
