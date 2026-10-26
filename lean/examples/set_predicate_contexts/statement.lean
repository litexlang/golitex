import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_set_x5f_predicate_x5f_contexts_x2f_statement_x2e_lit

universe u v1 v2 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17
variable {M : Litex.Semantics.{u}}

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_4 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_5 : Litex.IsSet _value_i2) (h_1 : Litex.Superset _value_i1 _value_i2), Litex.Superset _value_i1 _value_i2 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_4 _Host_i2 _rep_i2 _value_i2 h_5 h_1
          have h_2 : Litex.Superset _value_i1 _value_i2 :=
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

theorem h_16 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_18 : Litex.IsSet _value_i5) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_19 : Litex.IsSet _value_i6) (h_14 : ¬ Litex.Superset _value_i5 _value_i6), ¬ Litex.Superset _value_i5 _value_i6 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_18 _Host_i6 _rep_i6 _value_i6 h_19 h_14
          have h_15 : ¬ Litex.Superset _value_i5 _value_i6 :=
            (by
              litex_checked_step =>
                exact (
                  h_14
                )
            )
          exact h_15
        )
      )
  )

theorem h_26 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_29 : Litex.IsSet _value_i7) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_30 : Litex.IsSet _value_i8) (h_24 : Litex.ProperSubset _value_i7 _value_i8), Litex.ProperSubset _value_i7 _value_i8 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_29 _Host_i8 _rep_i8 _value_i8 h_30 h_24
          have h_31 : Litex.Subset _value_i7 _value_i8 :=
            (by
              litex_checked_step =>
                exact (
                  (h_24).1
                )
            )
          have h_32 : ¬ Litex.Same _value_i7 _value_i8 :=
            (by
              litex_checked_step =>
                exact (
                  (h_24).2
                )
            )
          have h_25 : Litex.ProperSubset _value_i7 _value_i8 :=
            (by
              litex_checked_step =>
                exact (
                  h_24
                )
            )
          have h_37 : Litex.Subset _value_i7 _value_i8 :=
            (by
              litex_checked_step =>
                exact (
                  (h_25).1
                )
            )
          have h_38 : ¬ Litex.Same _value_i7 _value_i8 :=
            (by
              litex_checked_step =>
                exact (
                  (h_25).2
                )
            )
          exact h_25
        )
      )
  )

theorem h_41 : ∀ {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_45 : Litex.IsSet _value_i9) {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_46 : Litex.IsSet _value_i10) (h_39 : ¬ Litex.ProperSubset _value_i9 _value_i10), ¬ Litex.ProperSubset _value_i9 _value_i10 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i9 _rep_i9 _value_i9 h_45 _Host_i10 _rep_i10 _value_i10 h_46 h_39
          have h_40 : ¬ Litex.ProperSubset _value_i9 _value_i10 :=
            (by
              litex_checked_step =>
                exact (
                  h_39
                )
            )
          exact h_40
        )
      )
  )

theorem h_53 : ∀ {_Host_i11 : Type v11} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_58 : Litex.IsSet _value_i11) {_Host_i12 : Type v12} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_59 : Litex.IsSet _value_i12) (h_51 : Litex.ProperSuperset _value_i11 _value_i12), Litex.ProperSuperset _value_i11 _value_i12 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i11 _rep_i11 _value_i11 h_58 _Host_i12 _rep_i12 _value_i12 h_59 h_51
          have h_60 : Litex.Subset _value_i12 _value_i11 :=
            (by
              litex_checked_step =>
                exact (
                  (h_51).1
                )
            )
          have h_61 : ¬ Litex.Same _value_i11 _value_i12 :=
            (by
              litex_checked_step =>
                exact (
                  (h_51).2
                )
            )
          have h_52 : Litex.ProperSuperset _value_i11 _value_i12 :=
            (by
              litex_checked_step =>
                exact (
                  h_51
                )
            )
          have h_66 : Litex.Subset _value_i12 _value_i11 :=
            (by
              litex_checked_step =>
                exact (
                  (h_52).1
                )
            )
          have h_67 : ¬ Litex.Same _value_i11 _value_i12 :=
            (by
              litex_checked_step =>
                exact (
                  (h_52).2
                )
            )
          exact h_52
        )
      )
  )

theorem h_70 : ∀ {_Host_i13 : Type v13} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_76 : Litex.IsSet _value_i13) {_Host_i14 : Type v14} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_77 : Litex.IsSet _value_i14) (h_68 : ¬ Litex.ProperSuperset _value_i13 _value_i14), ¬ Litex.ProperSuperset _value_i13 _value_i14 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i13 _rep_i13 _value_i13 h_76 _Host_i14 _rep_i14 _value_i14 h_77 h_68
          have h_69 : ¬ Litex.ProperSuperset _value_i13 _value_i14 :=
            (by
              litex_checked_step =>
                exact (
                  h_68
                )
            )
          exact h_69
        )
      )
  )

theorem h_84 : ∀ {_Host_i15 : Type v15} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_85 : Litex.IsSet _value_i15) (h_82 : ¬ Litex.IsSet _value_i15), ¬ Litex.IsSet _value_i15 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i15 _rep_i15 _value_i15 h_85 h_82
          have h_83 : ¬ Litex.IsSet _value_i15 :=
            (by
              litex_checked_step =>
                exact (
                  h_82
                )
            )
          exact h_83
        )
      )
  )

theorem h_90 : ∀ {_Host_i16 : Type v16} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_92 : Litex.IsSet _value_i16) (h_88 : ¬ Litex.IsNonempty _value_i16), ¬ Litex.IsNonempty _value_i16 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i16 _rep_i16 _value_i16 h_92 h_88
          have h_89 : ¬ Litex.IsNonempty _value_i16 :=
            (by
              litex_checked_step =>
                exact (
                  h_88
                )
            )
          exact h_89
        )
      )
  )

theorem h_97 : ∀ {_Host_i17 : Type v17} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_100 : Litex.IsSet _value_i17) (h_95 : ¬ Litex.IsFiniteSet _value_i17), ¬ Litex.IsFiniteSet _value_i17 :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i17 _rep_i17 _value_i17 h_100 h_95
          have h_96 : ¬ Litex.IsFiniteSet _value_i17 :=
            (by
              litex_checked_step =>
                exact (
                  h_95
                )
            )
          exact h_96
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_set_x5f_predicate_x5f_contexts_x2f_statement_x2e_lit
