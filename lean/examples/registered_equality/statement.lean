import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_registered_x5f_equality_x2f_statement_x2e_lit

universe u v1 v2 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
variable {M : Litex.Semantics.{u}}

def prop_1 {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) : Prop :=
  ∃ (h_2 : Litex.IsSet _value_i1), ∃ (h_3 : Litex.IsSet _value_i2), Litex.Same _value_i1 _value_i2

theorem h_5 : ∀ {_Host_i4 : Type v4} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_6 : Litex.IsSet _value_i4), ((prop_1 (M := M)) _value_i4 _value_i4) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i4 _rep_i4 _value_i4 h_6
          have h_4 : ((prop_1 (M := M)) _value_i4 _value_i4) :=
            (by
              litex_checked_step =>
                exact (
                  (Exists.intro h_6 (Exists.intro h_6 (show @Eq M.Value _ _ from Eq.refl _)))
                )
            )
          have h_15 :=
            (Classical.choose (show ((prop_1 (M := M)) _value_i4 _value_i4) from h_4))
          have h_16 :=
            (Classical.choose (Classical.choose_spec (show ((prop_1 (M := M)) _value_i4 _value_i4) from h_4)))
          have h_17 :=
            (Classical.choose_spec (Classical.choose_spec (show ((prop_1 (M := M)) _value_i4 _value_i4) from h_4)))
          exact h_4
        )
      )
  )

theorem h_20 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_21 : Litex.IsSet _value_i5) {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_22 : Litex.IsSet _value_i6) (h_18 : ((prop_1 (M := M)) _value_i5 _value_i6)), ((prop_1 (M := M)) _value_i6 _value_i5) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_21 _Host_i6 _rep_i6 _value_i6 h_22 h_18
          have h_23 :=
            (Classical.choose (show ((prop_1 (M := M)) _value_i5 _value_i6) from h_18))
          have h_24 :=
            (Classical.choose (Classical.choose_spec (show ((prop_1 (M := M)) _value_i5 _value_i6) from h_18)))
          have h_25 :=
            (Classical.choose_spec (Classical.choose_spec (show ((prop_1 (M := M)) _value_i5 _value_i6) from h_18)))
          have h_19 : ((prop_1 (M := M)) _value_i6 _value_i5) :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (∃ (_predicate_witness : (M.isSet _known_argument_0)), (∃ (_predicate_witness : (M.isSet _known_argument_1)), (_known_argument_0 = _known_argument_1)))) (Litex.denote _value_i6) (Litex.denote _value_i5)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (∃ (_predicate_witness : (M.isSet _known_argument_0)), (∃ (_predicate_witness : (M.isSet _known_argument_1)), (_known_argument_0 = _known_argument_1)))) (Litex.denote _value_i5) (Litex.denote _value_i6)) := h_18
                    exact Eq.mp (((((Eq.refl ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (∃ (_predicate_witness : (M.isSet _known_argument_0)), (∃ (_predicate_witness : (M.isSet _known_argument_1)), (_known_argument_0 = _known_argument_1)))) (Litex.denote _value_i5) (Litex.denote _value_i6)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (∃ (_predicate_witness : (M.isSet _known_argument_0)), (∃ (_predicate_witness : (M.isSet _known_argument_1)), (_known_argument_0 = _known_argument_1)))) _known_value (Litex.denote _value_i6))) h_25))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (∃ (_predicate_witness : (M.isSet _known_argument_0)), (∃ (_predicate_witness : (M.isSet _known_argument_1)), (_known_argument_0 = _known_argument_1)))) (Litex.denote _value_i6) _known_value)) (h_25).symm)) _known_citation
                  )
                )
            )
          have h_30 :=
            (Classical.choose (show ((prop_1 (M := M)) _value_i6 _value_i5) from h_19))
          have h_31 :=
            (Classical.choose (Classical.choose_spec (show ((prop_1 (M := M)) _value_i6 _value_i5) from h_19)))
          have h_32 :=
            (Classical.choose_spec (Classical.choose_spec (show ((prop_1 (M := M)) _value_i6 _value_i5) from h_19)))
          exact h_19
        )
      )
  )

theorem h_36 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_37 : Litex.IsSet _value_i7) {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_38 : Litex.IsSet _value_i8) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_39 : Litex.IsSet _value_i9) (h_33 : ((prop_1 (M := M)) _value_i7 _value_i8)) (h_34 : ((prop_1 (M := M)) _value_i8 _value_i9)), ((prop_1 (M := M)) _value_i7 _value_i9) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_37 _Host_i8 _rep_i8 _value_i8 h_38 _Host_i9 _rep_i9 _value_i9 h_39 h_33 h_34
          have h_40 :=
            (Classical.choose (show ((prop_1 (M := M)) _value_i7 _value_i8) from h_33))
          have h_41 :=
            (Classical.choose (Classical.choose_spec (show ((prop_1 (M := M)) _value_i7 _value_i8) from h_33)))
          have h_42 :=
            (Classical.choose_spec (Classical.choose_spec (show ((prop_1 (M := M)) _value_i7 _value_i8) from h_33)))
          have h_45 :=
            (Classical.choose (show ((prop_1 (M := M)) _value_i8 _value_i9) from h_34))
          have h_46 :=
            (Classical.choose (Classical.choose_spec (show ((prop_1 (M := M)) _value_i8 _value_i9) from h_34)))
          have h_47 :=
            (Classical.choose_spec (Classical.choose_spec (show ((prop_1 (M := M)) _value_i8 _value_i9) from h_34)))
          have h_35 : ((prop_1 (M := M)) _value_i7 _value_i9) :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (∃ (_predicate_witness : (M.isSet _known_argument_0)), (∃ (_predicate_witness : (M.isSet _known_argument_1)), (_known_argument_0 = _known_argument_1)))) (Litex.denote _value_i7) (Litex.denote _value_i9)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (∃ (_predicate_witness : (M.isSet _known_argument_0)), (∃ (_predicate_witness : (M.isSet _known_argument_1)), (_known_argument_0 = _known_argument_1)))) (Litex.denote _value_i7) (Litex.denote _value_i8)) := h_33
                    exact Eq.mp (((((Eq.refl ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (∃ (_predicate_witness : (M.isSet _known_argument_0)), (∃ (_predicate_witness : (M.isSet _known_argument_1)), (_known_argument_0 = _known_argument_1)))) (Litex.denote _value_i7) (Litex.denote _value_i8)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (∃ (_predicate_witness : (M.isSet _known_argument_0)), (∃ (_predicate_witness : (M.isSet _known_argument_1)), (_known_argument_0 = _known_argument_1)))) _known_value (Litex.denote _value_i8))) (show @Eq M.Value _ _ from Eq.refl _)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (∃ (_predicate_witness : (M.isSet _known_argument_0)), (∃ (_predicate_witness : (M.isSet _known_argument_1)), (_known_argument_0 = _known_argument_1)))) (Litex.denote _value_i7) _known_value)) h_47)) _known_citation
                  )
                )
            )
          have h_52 :=
            (Classical.choose (show ((prop_1 (M := M)) _value_i7 _value_i9) from h_35))
          have h_53 :=
            (Classical.choose (Classical.choose_spec (show ((prop_1 (M := M)) _value_i7 _value_i9) from h_35)))
          have h_54 :=
            (Classical.choose_spec (Classical.choose_spec (show ((prop_1 (M := M)) _value_i7 _value_i9) from h_35)))
          exact h_35
        )
      )
  )

theorem h_55 : ((prop_1 (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (Exists.intro (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Exists.intro (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (show @Eq M.Value _ _ from Eq.refl _)))
      )
  )

theorem h_60 : Litex.IsSet (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by rcases (h_55 (M := M)) with ⟨h_2, h_3, h_1⟩; exact h_2)
      )
  )

theorem h_61 : Litex.IsSet (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by rcases (h_55 (M := M)) with ⟨h_2, h_3, h_1⟩; exact h_3)
      )
  )

theorem h_62 : Litex.Same (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) :=
  (by
    litex_complete =>
      exact (
        (by rcases (h_55 (M := M)) with ⟨h_2, h_3, h_1⟩; exact h_1)
      )
  )

theorem h_66 : ∀ {_Host_i10 : Type v10} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_67 : Litex.IsSet _value_i10) {_Host_i11 : Type v11} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_68 : Litex.IsSet _value_i11) {_Host_i12 : Type v12} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_69 : Litex.IsSet _value_i12) (h_63 : ((prop_1 (M := M)) _value_i10 _value_i11)) (h_64 : ((prop_1 (M := M)) _value_i11 _value_i12)), ((prop_1 (M := M)) _value_i10 _value_i12) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i10 _rep_i10 _value_i10 h_67 _Host_i11 _rep_i11 _value_i11 h_68 _Host_i12 _rep_i12 _value_i12 h_69 h_63 h_64
          have h_71 :=
            (Classical.choose (show ((prop_1 (M := M)) _value_i10 _value_i11) from h_63))
          have h_72 :=
            (Classical.choose (Classical.choose_spec (show ((prop_1 (M := M)) _value_i10 _value_i11) from h_63)))
          have h_73 :=
            (Classical.choose_spec (Classical.choose_spec (show ((prop_1 (M := M)) _value_i10 _value_i11) from h_63)))
          have h_77 :=
            (Classical.choose (show ((prop_1 (M := M)) _value_i11 _value_i12) from h_64))
          have h_78 :=
            (Classical.choose (Classical.choose_spec (show ((prop_1 (M := M)) _value_i11 _value_i12) from h_64)))
          have h_79 :=
            (Classical.choose_spec (Classical.choose_spec (show ((prop_1 (M := M)) _value_i11 _value_i12) from h_64)))
          have h_65 : ((prop_1 (M := M)) _value_i10 _value_i12) :=
            (by
              litex_checked_step =>
                exact (
                  (show ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (∃ (_predicate_witness : (M.isSet _known_argument_0)), (∃ (_predicate_witness : (M.isSet _known_argument_1)), (_known_argument_0 = _known_argument_1)))) (Litex.denote _value_i10) (Litex.denote _value_i12)) from by
                    have _known_citation : ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (∃ (_predicate_witness : (M.isSet _known_argument_0)), (∃ (_predicate_witness : (M.isSet _known_argument_1)), (_known_argument_0 = _known_argument_1)))) (Litex.denote _value_i10) (Litex.denote _value_i11)) := h_63
                    exact Eq.mp (((((Eq.refl ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (∃ (_predicate_witness : (M.isSet _known_argument_0)), (∃ (_predicate_witness : (M.isSet _known_argument_1)), (_known_argument_0 = _known_argument_1)))) (Litex.denote _value_i10) (Litex.denote _value_i11)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (∃ (_predicate_witness : (M.isSet _known_argument_0)), (∃ (_predicate_witness : (M.isSet _known_argument_1)), (_known_argument_0 = _known_argument_1)))) _known_value (Litex.denote _value_i11))) (show @Eq M.Value _ _ from Eq.refl _)))).trans (congrArg (fun (_known_value : M.Value) => ((fun (_known_argument_0 : M.Value) (_known_argument_1 : M.Value) => (∃ (_predicate_witness : (M.isSet _known_argument_0)), (∃ (_predicate_witness : (M.isSet _known_argument_1)), (_known_argument_0 = _known_argument_1)))) (Litex.denote _value_i10) _known_value)) h_79)) _known_citation
                  )
                )
            )
          have h_84 :=
            (Classical.choose (show ((prop_1 (M := M)) _value_i10 _value_i12) from h_65))
          have h_85 :=
            (Classical.choose (Classical.choose_spec (show ((prop_1 (M := M)) _value_i10 _value_i12) from h_65)))
          have h_86 :=
            (Classical.choose_spec (Classical.choose_spec (show ((prop_1 (M := M)) _value_i10 _value_i12) from h_65)))
          exact h_65
        )
      )
  )

theorem h_88 : ∀ {_Host_i13 : Type v13} [_rep_i13 : Litex.Representation M _Host_i13] (_value_i13 : Litex.Obj (M := M) _Host_i13) (h_91 : Litex.IsSet _value_i13), ((prop_1 (M := M)) _value_i13 _value_i13) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i13 _rep_i13 _value_i13 h_91
          have h_93 : Litex.IsSet _value_i13 :=
            (by
              litex_checked_step =>
                exact (
                  h_91
                )
            )
          have h_90 : ∀ {_Host_i14 : Type _} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_94 : Litex.IsSet _value_i14), ((prop_1 (M := M)) _value_i14 _value_i14) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    intro _Host_i14 _rep_i14 _value_i14 h_94
                    have h_89 : ((prop_1 (M := M)) _value_i14 _value_i14) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Exists.intro h_94 (Exists.intro h_94 (show @Eq M.Value _ _ from Eq.refl _)))
                          )
                      )
                    have h_107 :=
                      (Classical.choose (show ((prop_1 (M := M)) _value_i14 _value_i14) from h_89))
                    have h_108 :=
                      (Classical.choose (Classical.choose_spec (show ((prop_1 (M := M)) _value_i14 _value_i14) from h_89)))
                    have h_109 :=
                      (Classical.choose_spec (Classical.choose_spec (show ((prop_1 (M := M)) _value_i14 _value_i14) from h_89)))
                    exact h_89
                  )
                )
            )
          exact (Exists.intro h_93 (Exists.intro h_93 (show @Eq M.Value _ _ from Eq.refl _)))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_registered_x5f_equality_x2f_statement_x2e_lit
