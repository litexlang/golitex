import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_range_x5f_bounds_x2f_statement_x2e_lit

universe u v1 v15 v38 v52 v75 v92 v118
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_3 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_5 : Litex.In _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_1 : (by
  have _sequence_domain : Litex.In _value_i1 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_5)
  exact Litex.SequenceBoundedAbove _value_i1)), (by
  let _atomic_wd_1_0 := (Litex.fnRange _value_i1 (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier) (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_5))
  exact Litex.RealBoundedAbove _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_5 h_1
          let _object_h6 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_6 : Litex.In _value_i1 _object_h6 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h6 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_5)
                )
            )
          have h_7 : (Litex.RealBoundedAboveValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i1))) :=
            (by
              litex_checked_step =>
                exact (
                  h_1
                )
            )
          have h_9 : (∃ (_value_i6 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i6) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i1)) (Litex.denote _value_i6))) :=
            (by
              litex_checked_step =>
                exact (
                  h_1
                )
            )
          have h_12 : Litex.In _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_5
                )
            )
          let _object_h13 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_13 : Litex.In _value_i1 _object_h13 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h13 (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_12)
                )
            )
          have h_14 : (Litex.RealBoundedAboveValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i1))) :=
            (by
              litex_checked_step =>
                exact (
                  h_1
                )
            )
          have h_16 : (∃ (_value_i10 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i10) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i1)) (Litex.denote _value_i10))) :=
            (by
              litex_checked_step =>
                exact (
                  h_1
                )
            )
          exact (by
            let _atomic_wd_1_0 := (Litex.fnRange _value_i1 (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier) (Litex.inOfSame _value_i1 _value_i1 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) (Litex.sameRefl _value_i1) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_12))
            exact h_14)
        )
      )
  )

theorem h_28 : ∀ {_Host_i15 : Type v15} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_30 : Litex.In _value_i15 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_26 : (by
  let _object_h31 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
  have h_31 : Litex.In _value_i15 _object_h31 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i15 _value_i15 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h31 (Litex.sameRefl _value_i15) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_30)
        )
    )
  exact (by
    let _atomic_wd_1_0 := (by
      have _range_signature_0 : Litex.In _value_i15 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i15 _value_i15 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_30)
      have _range_signature_1 : Litex.In _value_i15 (Litex.fnSet (_object_h31).val) := (Litex.inOfSame _value_i15 _value_i15 _object_h31 (Litex.fnSet (_object_h31).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_31)
      exact Litex.fnRange _value_i15 (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier) _range_signature_0)
    exact Litex.RealBoundedAbove _atomic_wd_1_0)
)), (by
  have _sequence_domain : Litex.In _value_i15 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i15 _value_i15 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_30)
  exact Litex.SequenceBoundedAbove _value_i15) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i15 _rep_i15 _value_i15 h_30 h_26
          let _object_h31 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_31 : Litex.In _value_i15 _object_h31 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i15 _value_i15 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h31 (Litex.sameRefl _value_i15) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_30)
                )
            )
          have h_36 : (∃ (_value_i21 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i21) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i15)) (Litex.denote _value_i21))) :=
            (by
              litex_checked_step =>
                exact (
                  h_26
                )
            )
          have h_38 : Litex.In _value_i15 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_30
                )
            )
          let _object_h39 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_39 : Litex.In _value_i15 _object_h39 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i15 _value_i15 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h39 (Litex.sameRefl _value_i15) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_38)
                )
            )
          have h_44 : (∃ (_value_i28 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i28) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i15)) (Litex.denote _value_i28))) :=
            (by
              litex_checked_step =>
                exact (
                  h_26
                )
            )
          exact (by
            have _sequence_domain : Litex.In _value_i15 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i15 _value_i15 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_38)
            exact (show (by
              let _atomic_wd_2_0 := (by
                have _range_signature_0 : Litex.In _value_i15 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i15 _value_i15 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_38)
                have _range_signature_1 : Litex.In _value_i15 (Litex.fnSet (_object_h39).val) := (Litex.inOfSame _value_i15 _value_i15 _object_h39 (Litex.fnSet (_object_h39).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_39)
                exact Litex.fnRange _value_i15 (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier) _range_signature_0)
              exact Litex.RealBoundedAbove _atomic_wd_2_0) from (by
              let _atomic_wd_2_0 := (by
                have _range_signature_0 : Litex.In _value_i15 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i15 _value_i15 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_38)
                have _range_signature_1 : Litex.In _value_i15 (Litex.fnSet (_object_h39).val) := (Litex.inOfSame _value_i15 _value_i15 _object_h39 (Litex.fnSet (_object_h39).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_39)
                exact Litex.fnRange _value_i15 (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier) _range_signature_0)
              exact h_26)))
        )
      )
  )

theorem h_58 : ∀ {_Host_i38 : Type v38} [_rep_i38 : Litex.Representation M _Host_i38] (_value_i38 : Litex.Obj (M := M) _Host_i38) (h_60 : Litex.In _value_i38 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_56 : (by
  have _sequence_domain : Litex.In _value_i38 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i38 _value_i38 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_60)
  exact Litex.SequenceBoundedBelow _value_i38)), (by
  let _atomic_wd_1_0 := (Litex.fnRange _value_i38 (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier) (Litex.inOfSame _value_i38 _value_i38 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) (Litex.sameRefl _value_i38) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_60))
  exact Litex.RealBoundedBelow _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i38 _rep_i38 _value_i38 h_60 h_56
          let _object_h61 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_61 : Litex.In _value_i38 _object_h61 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i38 _value_i38 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h61 (Litex.sameRefl _value_i38) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_60)
                )
            )
          have h_62 : (Litex.RealBoundedBelowValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i38))) :=
            (by
              litex_checked_step =>
                exact (
                  h_56
                )
            )
          have h_64 : (∃ (_value_i43 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i43) (M.standard Litex.StandardSetValue.real)), (Litex.RealLowerBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i38)) (Litex.denote _value_i43))) :=
            (by
              litex_checked_step =>
                exact (
                  h_56
                )
            )
          have h_67 : Litex.In _value_i38 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_60
                )
            )
          let _object_h68 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_68 : Litex.In _value_i38 _object_h68 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i38 _value_i38 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h68 (Litex.sameRefl _value_i38) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_67)
                )
            )
          have h_69 : (Litex.RealBoundedBelowValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i38))) :=
            (by
              litex_checked_step =>
                exact (
                  h_56
                )
            )
          have h_71 : (∃ (_value_i47 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i47) (M.standard Litex.StandardSetValue.real)), (Litex.RealLowerBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i38)) (Litex.denote _value_i47))) :=
            (by
              litex_checked_step =>
                exact (
                  h_56
                )
            )
          exact (by
            let _atomic_wd_1_0 := (Litex.fnRange _value_i38 (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier) (Litex.inOfSame _value_i38 _value_i38 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) (Litex.sameRefl _value_i38) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_67))
            exact h_69)
        )
      )
  )

theorem h_83 : ∀ {_Host_i52 : Type v52} [_rep_i52 : Litex.Representation M _Host_i52] (_value_i52 : Litex.Obj (M := M) _Host_i52) (h_85 : Litex.In _value_i52 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_81 : (by
  let _object_h86 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
  have h_86 : Litex.In _value_i52 _object_h86 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i52 _value_i52 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h86 (Litex.sameRefl _value_i52) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_85)
        )
    )
  exact (by
    let _atomic_wd_1_0 := (by
      have _range_signature_0 : Litex.In _value_i52 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i52 _value_i52 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_85)
      have _range_signature_1 : Litex.In _value_i52 (Litex.fnSet (_object_h86).val) := (Litex.inOfSame _value_i52 _value_i52 _object_h86 (Litex.fnSet (_object_h86).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_86)
      exact Litex.fnRange _value_i52 (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier) _range_signature_0)
    exact Litex.RealBoundedBelow _atomic_wd_1_0)
)), (by
  have _sequence_domain : Litex.In _value_i52 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i52 _value_i52 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_85)
  exact Litex.SequenceBoundedBelow _value_i52) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i52 _rep_i52 _value_i52 h_85 h_81
          let _object_h86 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_86 : Litex.In _value_i52 _object_h86 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i52 _value_i52 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h86 (Litex.sameRefl _value_i52) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_85)
                )
            )
          have h_91 : (∃ (_value_i58 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i58) (M.standard Litex.StandardSetValue.real)), (Litex.RealLowerBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i52)) (Litex.denote _value_i58))) :=
            (by
              litex_checked_step =>
                exact (
                  h_81
                )
            )
          have h_93 : Litex.In _value_i52 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_85
                )
            )
          let _object_h94 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_94 : Litex.In _value_i52 _object_h94 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i52 _value_i52 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h94 (Litex.sameRefl _value_i52) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_93)
                )
            )
          have h_99 : (∃ (_value_i65 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i65) (M.standard Litex.StandardSetValue.real)), (Litex.RealLowerBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i52)) (Litex.denote _value_i65))) :=
            (by
              litex_checked_step =>
                exact (
                  h_81
                )
            )
          exact (by
            have _sequence_domain : Litex.In _value_i52 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i52 _value_i52 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_93)
            exact (show (by
              let _atomic_wd_2_0 := (by
                have _range_signature_0 : Litex.In _value_i52 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i52 _value_i52 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_93)
                have _range_signature_1 : Litex.In _value_i52 (Litex.fnSet (_object_h94).val) := (Litex.inOfSame _value_i52 _value_i52 _object_h94 (Litex.fnSet (_object_h94).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_94)
                exact Litex.fnRange _value_i52 (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier) _range_signature_0)
              exact Litex.RealBoundedBelow _atomic_wd_2_0) from (by
              let _atomic_wd_2_0 := (by
                have _range_signature_0 : Litex.In _value_i52 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i52 _value_i52 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_93)
                have _range_signature_1 : Litex.In _value_i52 (Litex.fnSet (_object_h94).val) := (Litex.inOfSame _value_i52 _value_i52 _object_h94 (Litex.fnSet (_object_h94).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_94)
                exact Litex.fnRange _value_i52 (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier) _range_signature_0)
              exact h_81)))
        )
      )
  )

theorem h_113 : ∀ {_Host_i75 : Type v75} [_rep_i75 : Litex.Representation M _Host_i75] (_value_i75 : Litex.Obj (M := M) _Host_i75) (h_115 : Litex.In _value_i75 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_111 : (by
  have _sequence_domain : Litex.In _value_i75 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i75 _value_i75 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_115)
  exact Litex.SequenceBounded _value_i75)), (by
  let _atomic_wd_1_0 := (Litex.fnRange _value_i75 (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier) (Litex.inOfSame _value_i75 _value_i75 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) (Litex.sameRefl _value_i75) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_115))
  exact Litex.RealBounded _atomic_wd_1_0) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i75 _rep_i75 _value_i75 h_115 h_111
          let _object_h116 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_116 : Litex.In _value_i75 _object_h116 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i75 _value_i75 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h116 (Litex.sameRefl _value_i75) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_115)
                )
            )
          have h_117 : (Litex.RealBoundedValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i75))) :=
            (by
              litex_checked_step =>
                exact (
                  h_111
                )
            )
          have h_119 : (∃ (_value_i80 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i80) (M.standard Litex.StandardSetValue.real)), (Litex.RealLowerBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i75)) (Litex.denote _value_i80))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_111).1
                )
            )
          have h_121 : (∃ (_value_i81 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i81) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i75)) (Litex.denote _value_i81))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_111).2
                )
            )
          have h_122 : (Litex.SequenceBoundedAboveValue M (Litex.denote _value_i75)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_111).2
                )
            )
          have h_123 : (Litex.SequenceBoundedBelowValue M (Litex.denote _value_i75)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_111).1
                )
            )
          have h_126 : Litex.In _value_i75 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_115
                )
            )
          let _object_h127 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_127 : Litex.In _value_i75 _object_h127 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i75 _value_i75 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h127 (Litex.sameRefl _value_i75) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_126)
                )
            )
          have h_128 : (Litex.RealBoundedValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i75))) :=
            (by
              litex_checked_step =>
                exact (
                  h_111
                )
            )
          have h_130 : (∃ (_value_i85 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i85) (M.standard Litex.StandardSetValue.real)), (Litex.RealLowerBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i75)) (Litex.denote _value_i85))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_111).1
                )
            )
          have h_132 : (∃ (_value_i86 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i86) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i75)) (Litex.denote _value_i86))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_111).2
                )
            )
          have h_133 : (Litex.SequenceBoundedAboveValue M (Litex.denote _value_i75)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_111).2
                )
            )
          have h_134 : (Litex.SequenceBoundedBelowValue M (Litex.denote _value_i75)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_111).1
                )
            )
          exact (by
            let _atomic_wd_1_0 := (Litex.fnRange _value_i75 (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier) (Litex.inOfSame _value_i75 _value_i75 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) (Litex.sameRefl _value_i75) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_126))
            exact h_128)
        )
      )
  )

theorem h_150 : ∀ {_Host_i92 : Type v92} [_rep_i92 : Litex.Representation M _Host_i92] (_value_i92 : Litex.Obj (M := M) _Host_i92) (h_152 : Litex.In _value_i92 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_148 : (by
  let _object_h153 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
  have h_153 : Litex.In _value_i92 _object_h153 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i92 _value_i92 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h153 (Litex.sameRefl _value_i92) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_152)
        )
    )
  exact (by
    let _atomic_wd_1_0 := (by
      have _range_signature_0 : Litex.In _value_i92 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i92 _value_i92 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_152)
      have _range_signature_1 : Litex.In _value_i92 (Litex.fnSet (_object_h153).val) := (Litex.inOfSame _value_i92 _value_i92 _object_h153 (Litex.fnSet (_object_h153).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_153)
      exact Litex.fnRange _value_i92 (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier) _range_signature_0)
    exact Litex.RealBounded _atomic_wd_1_0)
)), (by
  have _sequence_domain : Litex.In _value_i92 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i92 _value_i92 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_152)
  exact Litex.SequenceBounded _value_i92) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i92 _rep_i92 _value_i92 h_152 h_148
          let _object_h153 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_153 : Litex.In _value_i92 _object_h153 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i92 _value_i92 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h153 (Litex.sameRefl _value_i92) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_152)
                )
            )
          have h_158 : (∃ (_value_i98 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i98) (M.standard Litex.StandardSetValue.real)), (Litex.RealLowerBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i92)) (Litex.denote _value_i98))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_148).1
                )
            )
          have h_160 : (∃ (_value_i99 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i99) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i92)) (Litex.denote _value_i99))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_148).2
                )
            )
          have h_161 : (Litex.RealBoundedAboveValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i92))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_148).2
                )
            )
          have h_162 : (Litex.RealBoundedBelowValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i92))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_148).1
                )
            )
          have h_164 : Litex.In _value_i92 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_152
                )
            )
          let _object_h165 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_165 : Litex.In _value_i92 _object_h165 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i92 _value_i92 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h165 (Litex.sameRefl _value_i92) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_164)
                )
            )
          have h_170 : (∃ (_value_i106 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i106) (M.standard Litex.StandardSetValue.real)), (Litex.RealLowerBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i92)) (Litex.denote _value_i106))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_148).1
                )
            )
          have h_172 : (∃ (_value_i107 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i107) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i92)) (Litex.denote _value_i107))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_148).2
                )
            )
          have h_173 : (Litex.RealBoundedAboveValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i92))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_148).2
                )
            )
          have h_174 : (Litex.RealBoundedBelowValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i92))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_148).1
                )
            )
          exact (by
            have _sequence_domain : Litex.In _value_i92 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i92 _value_i92 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_164)
            exact (show (by
              let _atomic_wd_2_0 := (by
                have _range_signature_0 : Litex.In _value_i92 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i92 _value_i92 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_164)
                have _range_signature_1 : Litex.In _value_i92 (Litex.fnSet (_object_h165).val) := (Litex.inOfSame _value_i92 _value_i92 _object_h165 (Litex.fnSet (_object_h165).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_165)
                exact Litex.fnRange _value_i92 (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier) _range_signature_0)
              exact Litex.RealBounded _atomic_wd_2_0) from (by
              let _atomic_wd_2_0 := (by
                have _range_signature_0 : Litex.In _value_i92 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i92 _value_i92 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_164)
                have _range_signature_1 : Litex.In _value_i92 (Litex.fnSet (_object_h165).val) := (Litex.inOfSame _value_i92 _value_i92 _object_h165 (Litex.fnSet (_object_h165).val) ((show @Eq M.Value _ _ from Eq.refl _)).symm (show @Eq M.Value _ _ from Eq.refl _) h_165)
                exact Litex.fnRange _value_i92 (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier) _range_signature_0)
              exact h_148)))
        )
      )
  )

theorem h_197 : ∀ {_Host_i118 : Type v118} [_rep_i118 : Litex.Representation M _Host_i118] (_value_i118 : Litex.Obj (M := M) _Host_i118) (h_217 : Litex.In _value_i118 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) (h_190 : (by
  have _sequence_domain : Litex.In _value_i118 (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) := (Litex.inOfSame _value_i118 _value_i118 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) ((show @Eq M.Value _ _ from Eq.refl _)).symm ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))))) h_217)
  exact Litex.SequenceBounded _value_i118)), ((Litex.SequenceBoundedAbove _value_i118) ∧ (((Litex.SequenceBoundedBelow _value_i118) ∧ (((∃ (_value_i119 : Litex.Obj (M := M) M.Value), ∃ (h_236 : Litex.In _value_i119 (Litex.R (M := M))), Litex.RealUpperBound (Litex.fnRange _value_i118 (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier) (Litex.inOfSame _value_i118 _value_i118 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) (Litex.sameRefl _value_i118) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_217)) _value_i119) ∧ (∃ (_value_i120 : Litex.Obj (M := M) M.Value), ∃ (h_247 : Litex.In _value_i120 (Litex.R (M := M))), Litex.RealLowerBound (Litex.fnRange _value_i118 (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier) (Litex.inOfSame _value_i118 _value_i118 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) (Litex.sameRefl _value_i118) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_217)) _value_i120)))))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i118 _rep_i118 _value_i118 h_217 h_190
          let _object_h218 := (Litex.fnSet (Litex.seqSignature (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))).val.carrier))
          have h_218 : Litex.In _value_i118 _object_h218 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i118 _value_i118 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) _object_h218 (Litex.sameRefl _value_i118) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_217)
                )
            )
          have h_219 : (Litex.RealBoundedValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i118))) :=
            (by
              litex_checked_step =>
                exact (
                  h_190
                )
            )
          have h_221 : (∃ (_value_i124 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i124) (M.standard Litex.StandardSetValue.real)), (Litex.RealLowerBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i118)) (Litex.denote _value_i124))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_190).1
                )
            )
          have h_223 : (∃ (_value_i125 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i125) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i118)) (Litex.denote _value_i125))) :=
            (by
              litex_checked_step =>
                exact (
                  (h_190).2
                )
            )
          have h_224 : (Litex.SequenceBoundedAboveValue M (Litex.denote _value_i118)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_190).2
                )
            )
          have h_225 : (Litex.SequenceBoundedBelowValue M (Litex.denote _value_i118)) :=
            (by
              litex_checked_step =>
                exact (
                  (h_190).1
                )
            )
          have h_191 : Litex.SequenceBoundedAbove _value_i118 :=
            (by
              litex_checked_step =>
                exact (
                  h_224
                )
            )
          have h_228 : (Litex.RealBoundedAboveValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i118))) :=
            (by
              litex_checked_step =>
                exact (
                  h_191
                )
            )
          have h_230 : (∃ (_value_i126 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i126) (M.standard Litex.StandardSetValue.real)), (Litex.RealUpperBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i118)) (Litex.denote _value_i126))) :=
            (by
              litex_checked_step =>
                exact (
                  h_191
                )
            )
          have h_192 : Litex.SequenceBoundedBelow _value_i118 :=
            (by
              litex_checked_step =>
                exact (
                  h_225
                )
            )
          have h_233 : (Litex.RealBoundedBelowValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i118))) :=
            (by
              litex_checked_step =>
                exact (
                  h_192
                )
            )
          have h_235 : (∃ (_value_i127 : Litex.Obj (M := M) M.Value), ∃ (_ : M.mem (Litex.denote _value_i127) (M.standard Litex.StandardSetValue.real)), (Litex.RealLowerBoundValue M (Litex.FunctionSemantics.rangeValue (Litex.denote _value_i118)) (Litex.denote _value_i127))) :=
            (by
              litex_checked_step =>
                exact (
                  h_192
                )
            )
          have h_194 : ∃ (_value_i119 : Litex.Obj (M := M) M.Value), ∃ (h_236 : Litex.In _value_i119 (Litex.R (M := M))), Litex.RealUpperBound (Litex.fnRange _value_i118 (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier) (Litex.inOfSame _value_i118 _value_i118 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) (Litex.sameRefl _value_i118) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_217)) _value_i119 :=
            (by
              litex_checked_step =>
                exact (
                  h_223
                )
            )
          have h_196 : ∃ (_value_i120 : Litex.Obj (M := M) M.Value), ∃ (h_247 : Litex.In _value_i120 (Litex.R (M := M))), Litex.RealLowerBound (Litex.fnRange _value_i118 (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier) (Litex.inOfSame _value_i118 _value_i118 (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M)))) (Litex.fnSet (Litex.seqSignature ((Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))).val.carrier)) (Litex.sameRefl _value_i118) (Litex.seqSet_eq_fnSet (Litex.seqSet (Litex.R (M := M)) (Litex.isSet (Litex.R (M := M))))) h_217)) _value_i120 :=
            (by
              litex_checked_step =>
                exact (
                  h_221
                )
            )
          exact (And.intro h_191 (And.intro h_192 (And.intro h_194 h_196)))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_range_x5f_bounds_x2f_statement_x2e_lit
