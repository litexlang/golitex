import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_monotonicity_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => _raw_i2) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → M.mem ((fun (_raw_i2 : M.Value) => _raw_i2) _raw_i2) (Litex.denote (Litex.R (M := M))) := (by
    intro _raw_i2 h_14 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
    have h_14 : Litex.In _value_i2 (Litex.NPos (M := M)) := h_14
    have h_15 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inNPos_positive _value_i2 h_14)
          )
      )
    have h_16 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i2 h_15)
          )
      )
    have h_17 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i2 h_15) _litex_zero.symm)
          )
      )
    change Litex.In _value_i2 (Litex.R (M := M))
    exact (Litex.naturalToReal _value_i2 (Litex.inNPos_natural _value_i2 h_14)))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.NPos (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard))
theorem h_43 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_44 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem h_45 : (by
  have _sequence_domain : Litex.In (_object_i1 (M := M)) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
  exact Litex.SequenceNondecreasing (_object_i1 (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          have _sequence_domain : Litex.In (_object_i1 (M := M)) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
          exact (Litex.sequenceOrderOfForall false false (_object_i1 (M := M)) (show ∀ {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_61 : Litex.In _value_i4 (Litex.NPos (M := M))) {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_65 : Litex.In _value_i5 (Litex.NPos (M := M))) (h_46 : Litex.Le _value_i4 _value_i5), (by
            let _object_w10 := (let _litex_call_arg_0 := _value_i4;
            Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_43 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_61, True.intro⟩))
            let _object_w11 := (let _litex_call_arg_0 := _value_i5;
            Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_43 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_65, True.intro⟩))
            exact (by
              let _atomic_wd_2_0 := _object_w10
              let _atomic_wd_2_1 := _object_w11
              exact Litex.Le _atomic_wd_2_0 _atomic_wd_2_1)
          ) from (by
            intro _Host_i4 _rep_i4 _value_i4 h_61 _Host_i5 _rep_i5 _value_i5 h_65 h_46
            have h_62 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inNPos_positive _value_i4 h_61)
                  )
              )
            have h_63 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i4 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.ltToLe (Litex.number (M := M) 0) _value_i4 h_62)
                  )
              )
            have h_64 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i4 h_62) _litex_zero.symm)
                  )
              )
            have h_66 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inNPos_positive _value_i5 h_65)
                  )
              )
            have h_67 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.ltToLe (Litex.number (M := M) 0) _value_i5 h_66)
                  )
              )
            have h_68 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i5 h_66) _litex_zero.symm)
                  )
              )
            have h_129 : Litex.In _value_i5 (Litex.N (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.weakIntegerLowerBoundInN _value_i4 _value_i5 (Litex.naturalToInteger _value_i5 (Litex.inNPos_natural _value_i5 h_65)) h_63 h_46)
                  )
              )
            let _object_w10 := (let _litex_call_arg_0 := _value_i4;
            Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_43 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_61, True.intro⟩))
            let _object_w11 := (let _litex_call_arg_0 := _value_i5;
            Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_43 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_65, True.intro⟩))
            have h_47 : (by
              let _atomic_wd_2_0 := _object_w10
              let _atomic_wd_2_1 := _object_w11
              exact Litex.Le _atomic_wd_2_0 _atomic_wd_2_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      let _atomic_wd_2_0 := _object_w10
                      let _atomic_wd_2_1 := _object_w11
                      exact (by
                        change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r ≤ _s)) (Litex.denote _atomic_wd_2_0) (Litex.denote _atomic_wd_2_1)
                        have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r ≤ _s)) (Litex.denote _value_i4) (Litex.denote _value_i5) := h_46
                        exact Eq.mp (((((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r ≤ _s)) (Litex.denote _value_i4) (Litex.denote _value_i5)))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r ≤ _s)) _unfold_value (Litex.denote _value_i5)) ((let _equal_wd_1_0 := _atomic_wd_2_0;
                      (show Litex.Same _equal_wd_1_0 _value_i4 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i4)) = (Litex.denote _value_i4) from by
                        have _litex_residual : (Litex.denote _value_i4) = (Litex.denote _value_i4) := (show @Eq M.Value _ _ from Eq.refl _)
                        exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i4)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i4)) = (Litex.denote _value_i4) from by
                        let _litex_original := _equal_wd_1_0
                        let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                      let _wd_1_1 := _value_i4;
                      (let _litex_call_arg_0 := _wd_1_1;
                      Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) h_61 True.intro))
                        have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_44 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                        have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                        exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => _raw_i2) _litex_input) (Litex.denote _litex_literal.val.argument) = (Litex.denote _value_i4); exact rfl))
                      ))).trans _litex_residual)))).symm))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r ≤ _s)) (Litex.denote _atomic_wd_2_0) _unfold_value) ((let _equal_wd_1_0 := _atomic_wd_2_1;
                      (show Litex.Same _equal_wd_1_0 _value_i5 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i5)) = (Litex.denote _value_i5) from by
                        have _litex_residual : (Litex.denote _value_i5) = (Litex.denote _value_i5) := (show @Eq M.Value _ _ from Eq.refl _)
                        exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i5)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i5)) = (Litex.denote _value_i5) from by
                        let _litex_original := _equal_wd_1_0
                        let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                      let _wd_1_1 := _value_i5;
                      (let _litex_call_arg_0 := _wd_1_1;
                      Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) h_65 True.intro))
                        have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_44 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                        have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                        exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => _raw_i2) _litex_input) (Litex.denote _litex_literal.val.argument) = (Litex.denote _value_i5); exact rfl))
                      ))).trans _litex_residual)))).symm)) _unfold_child
                      ))
                  )
              )
            exact h_47
          ))))
      )
  )

theorem h_2507 : ∀ {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (_member_i8 : Litex.In _value_i8 (Litex.NPos (M := M))) {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (_member_i9 : Litex.In _value_i9 (Litex.NPos (M := M))) (h_2505 : (∃ (_r _s : ℝ), (Litex.denote _value_i8) = M.number (_r : ℂ) ∧ (Litex.denote _value_i9) = M.number (_s : ℂ) ∧ _r ≤ _s)), (∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i8)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i9)) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
  (by
    litex_complete =>
      exact (
        (fun {_Host_i8 : Type _} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (_member_i8 : Litex.In _value_i8 (Litex.NPos (M := M))) {_Host_i9 : Type _} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (_member_i9 : Litex.In _value_i9 (Litex.NPos (M := M))) (h_2505 : (∃ (_r _s : ℝ), (Litex.denote _value_i8) = M.number (_r : ℂ) ∧ (Litex.denote _value_i9) = M.number (_s : ℂ) ∧ _r ≤ _s)) => ((h_45 (M := M))) (Litex.denote _value_i8) _member_i8 (Litex.denote _value_i9) _member_i9 h_2505)
      )
  )

theorem h_2508 : (by
  have _sequence_domain : Litex.In (_object_i1 (M := M)) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
  exact Litex.SequenceStrictlyIncreasing (_object_i1 (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          have _sequence_domain : Litex.In (_object_i1 (M := M)) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))) := (Litex.inOfSame (_object_i1 (M := M)) (_object_i1 (M := M)) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input))) ((h_44 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i1 (M := M))))
          exact (Litex.sequenceOrderOfForall true false (_object_i1 (M := M)) (show ∀ {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_2525 : Litex.In _value_i11 (Litex.NPos (M := M))) {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_2529 : Litex.In _value_i12 (Litex.NPos (M := M))) (h_2509 : Litex.Lt _value_i11 _value_i12), (by
            let _object_w14 := (let _litex_call_arg_0 := _value_i11;
            Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_43 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_2525, True.intro⟩))
            let _object_w15 := (let _litex_call_arg_0 := _value_i12;
            Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_43 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_2529, True.intro⟩))
            exact (by
              let _atomic_wd_2_0 := _object_w14
              let _atomic_wd_2_1 := _object_w15
              exact Litex.Lt _atomic_wd_2_0 _atomic_wd_2_1)
          ) from (by
            intro _Host_i11 _rep_i11 _value_i11 h_2525 _Host_i12 _rep_i12 _value_i12 h_2529 h_2509
            have h_2526 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i11 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inNPos_positive _value_i11 h_2525)
                  )
              )
            have h_2527 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i11 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.ltToLe (Litex.number (M := M) 0) _value_i11 h_2526)
                  )
              )
            have h_2528 : ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i11 h_2526) _litex_zero.symm)
                  )
              )
            have h_2530 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i12 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inNPos_positive _value_i12 h_2529)
                  )
              )
            have h_2531 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i12 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.ltToLe (Litex.number (M := M) 0) _value_i12 h_2530)
                  )
              )
            have h_2532 : ¬ Litex.Same _value_i12 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i12 h_2530) _litex_zero.symm)
                  )
              )
            have h_2598 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i12 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) _value_i11 _value_i12 h_2527 h_2509)
                  )
              )
            let _object_w14 := (let _litex_call_arg_0 := _value_i11;
            Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_43 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_2525, True.intro⟩))
            let _object_w15 := (let _litex_call_arg_0 := _value_i12;
            Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_43 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_2529, True.intro⟩))
            have h_2510 : (by
              let _atomic_wd_2_0 := _object_w14
              let _atomic_wd_2_1 := _object_w15
              exact Litex.Lt _atomic_wd_2_0 _atomic_wd_2_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      let _atomic_wd_2_0 := _object_w14
                      let _atomic_wd_2_1 := _object_w15
                      exact (by
                        change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.denote _atomic_wd_2_0) (Litex.denote _atomic_wd_2_1)
                        have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.denote _value_i11) (Litex.denote _value_i12) := h_2509
                        exact Eq.mp (((((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.denote _value_i11) (Litex.denote _value_i12)))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r < _s)) _unfold_value (Litex.denote _value_i12)) ((let _equal_wd_1_0 := _atomic_wd_2_0;
                      (show Litex.Same _equal_wd_1_0 _value_i11 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i11)) = (Litex.denote _value_i11) from by
                        have _litex_residual : (Litex.denote _value_i11) = (Litex.denote _value_i11) := (show @Eq M.Value _ _ from Eq.refl _)
                        exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i11)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i11)) = (Litex.denote _value_i11) from by
                        let _litex_original := _equal_wd_1_0
                        let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                      let _wd_1_1 := _value_i11;
                      (let _litex_call_arg_0 := _wd_1_1;
                      Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) h_2525 True.intro))
                        have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_44 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                        have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                        exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => _raw_i2) _litex_input) (Litex.denote _litex_literal.val.argument) = (Litex.denote _value_i11); exact rfl))
                      ))).trans _litex_residual)))).symm))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.denote _atomic_wd_2_0) _unfold_value) ((let _equal_wd_1_0 := _atomic_wd_2_1;
                      (show Litex.Same _equal_wd_1_0 _value_i12 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i12)) = (Litex.denote _value_i12) from by
                        have _litex_residual : (Litex.denote _value_i12) = (Litex.denote _value_i12) := (show @Eq M.Value _ _ from Eq.refl _)
                        exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i12)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i12)) = (Litex.denote _value_i12) from by
                        let _litex_original := _equal_wd_1_0
                        let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                      let _wd_1_1 := _value_i12;
                      (let _litex_call_arg_0 := _wd_1_1;
                      Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) h_2529 True.intro))
                        have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_44 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                        have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                        exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => _raw_i2) _litex_input) (Litex.denote _litex_literal.val.argument) = (Litex.denote _value_i12); exact rfl))
                      ))).trans _litex_residual)))).symm)) _unfold_child
                      ))
                  )
              )
            exact h_2510
          ))))
      )
  )

theorem h_3836 : ∀ {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (_member_i15 : Litex.In _value_i15 (Litex.NPos (M := M))) {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (_member_i16 : Litex.In _value_i16 (Litex.NPos (M := M))) (h_3834 : (∃ (_r _s : ℝ), (Litex.denote _value_i15) = M.number (_r : ℂ) ∧ (Litex.denote _value_i16) = M.number (_s : ℂ) ∧ _r < _s)), (∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i15)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i16)) = M.number (_s : ℂ) ∧ _r < _s) :=
  (by
    litex_complete =>
      exact (
        (fun {_Host_i15 : Type _} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (_member_i15 : Litex.In _value_i15 (Litex.NPos (M := M))) {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (_member_i16 : Litex.In _value_i16 (Litex.NPos (M := M))) (h_3834 : (∃ (_r _s : ℝ), (Litex.denote _value_i15) = M.number (_r : ℂ) ∧ (Litex.denote _value_i16) = M.number (_s : ℂ) ∧ _r < _s)) => ((h_2508 (M := M))) (Litex.denote _value_i15) _member_i15 (Litex.denote _value_i16) _member_i16 h_3834)
      )
  )

noncomputable def _object_i17 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => (M.negValue _raw_i18)) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i18 : M.Value), M.mem _raw_i18 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i18 : M.Value) => True) _raw_i18) → M.mem ((fun (_raw_i18 : M.Value) => (M.negValue _raw_i18)) _raw_i18) (Litex.denote (Litex.R (M := M))) := (by
    intro _raw_i18 h_3850 _
    let _value_i18 := Litex.semanticObject (M := M) _raw_i18 (M.member_isSet h_3850)
    have h_3850 : Litex.In _value_i18 (Litex.NPos (M := M)) := h_3850
    have h_3851 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i18 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inNPos_positive _value_i18 h_3850)
          )
      )
    have h_3852 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i18 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i18 h_3851)
          )
      )
    have h_3853 : ¬ Litex.Same _value_i18 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i18 h_3851) _litex_zero.symm)
          )
      )
    change (by
      let _atomic_wd_1_0 := (Litex.neg _value_i18 (Litex.naturalToComplex _value_i18 (Litex.inNPos_natural _value_i18 h_3850)))
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.neg _value_i18 (Litex.naturalToComplex _value_i18 (Litex.inNPos_natural _value_i18 h_3850)))
      exact (Litex.negInR _value_i18 (Litex.naturalToReal _value_i18 (Litex.inNPos_natural _value_i18 h_3850)))))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.NPos (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard))
theorem h_3938 : Litex.In (_object_i17 (M := M)) (Litex.fnSet ((_object_i17 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i17 (M := M)))
      )
  )
theorem h_3939 : Litex.Same (_object_i17 (M := M)) (_object_i17 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i17 (M := M)))
      )
  )

theorem h_3940 : (by
  have _sequence_domain : Litex.In (_object_i17 (M := M)) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => True) _litex_input))) := (Litex.inOfSame (_object_i17 (M := M)) (_object_i17 (M := M)) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => True) _litex_input))) ((h_3939 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i17 (M := M))))
  exact Litex.SequenceNonincreasing (_object_i17 (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          have _sequence_domain : Litex.In (_object_i17 (M := M)) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => True) _litex_input))) := (Litex.inOfSame (_object_i17 (M := M)) (_object_i17 (M := M)) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => True) _litex_input))) ((h_3939 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i17 (M := M))))
          exact (Litex.sequenceOrderOfForall false true (_object_i17 (M := M)) (show ∀ {_Host_i20 : Type _} [_rep_i20 : Litex.Representation M _Host_i20] (_value_i20 : Litex.Obj (M := M) _Host_i20) (h_3959 : Litex.In _value_i20 (Litex.NPos (M := M))) {_Host_i21 : Type _} [_rep_i21 : Litex.Representation M _Host_i21] (_value_i21 : Litex.Obj (M := M) _Host_i21) (h_3963 : Litex.In _value_i21 (Litex.NPos (M := M))) (h_3941 : Litex.Le _value_i20 _value_i21), (by
            let _object_w25 := (let _litex_call_arg_0 := _value_i21;
            Litex.callOn ((_object_i17 (M := M))).val.signature (_object_i17 (M := M)) _litex_call_arg_0 (h_3938 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_3963, True.intro⟩))
            let _object_w26 := (let _litex_call_arg_0 := _value_i20;
            Litex.callOn ((_object_i17 (M := M))).val.signature (_object_i17 (M := M)) _litex_call_arg_0 (h_3938 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_3959, True.intro⟩))
            exact (by
              let _atomic_wd_2_0 := _object_w25
              let _atomic_wd_2_1 := _object_w26
              exact Litex.Le _atomic_wd_2_0 _atomic_wd_2_1)
          ) from (by
            intro _Host_i20 _rep_i20 _value_i20 h_3959 _Host_i21 _rep_i21 _value_i21 h_3963 h_3941
            have h_3960 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i20 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inNPos_positive _value_i20 h_3959)
                  )
              )
            have h_3961 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i20 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.ltToLe (Litex.number (M := M) 0) _value_i20 h_3960)
                  )
              )
            have h_3962 : ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i20 h_3960) _litex_zero.symm)
                  )
              )
            have h_3964 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i21 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inNPos_positive _value_i21 h_3963)
                  )
              )
            have h_3965 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i21 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.ltToLe (Litex.number (M := M) 0) _value_i21 h_3964)
                  )
              )
            have h_3966 : ¬ Litex.Same _value_i21 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i21 h_3964) _litex_zero.symm)
                  )
              )
            have h_4035 : Litex.In _value_i21 (Litex.N (M := M)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.weakIntegerLowerBoundInN _value_i20 _value_i21 (Litex.naturalToInteger _value_i21 (Litex.inNPos_natural _value_i21 h_3963)) h_3961 h_3941)
                  )
              )
            let _object_w25 := (let _litex_call_arg_0 := _value_i21;
            Litex.callOn ((_object_i17 (M := M))).val.signature (_object_i17 (M := M)) _litex_call_arg_0 (h_3938 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_3963, True.intro⟩))
            let _object_w26 := (let _litex_call_arg_0 := _value_i20;
            Litex.callOn ((_object_i17 (M := M))).val.signature (_object_i17 (M := M)) _litex_call_arg_0 (h_3938 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_3959, True.intro⟩))
            have h_3942 : (by
              let _atomic_wd_2_0 := _object_w25
              let _atomic_wd_2_1 := _object_w26
              exact Litex.Le _atomic_wd_2_0 _atomic_wd_2_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      let _atomic_wd_2_0 := _object_w25
                      let _atomic_wd_2_1 := _object_w26
                      exact (by
                        change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r ≤ _s)) (Litex.denote _atomic_wd_2_0) (Litex.denote _atomic_wd_2_1)
                        have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r ≤ _s)) (Litex.denote (Litex.neg _value_i21 (Litex.naturalToComplex _value_i21 h_4035))) (Litex.denote (Litex.neg _value_i20 (Litex.naturalToComplex _value_i20 (Litex.inNPos_natural _value_i20 h_3959)))) := (by
                        let _atomic_wd_3_0 := (Litex.neg _value_i21 (Litex.naturalToComplex _value_i21 h_4035))
                        let _atomic_wd_3_1 := (Litex.neg _value_i20 (Litex.naturalToComplex _value_i20 (Litex.inNPos_natural _value_i20 h_3959)))
                        exact (Litex.negationWeakOrder _atomic_wd_3_0 _atomic_wd_3_1 h_3941))
                        exact Eq.mp (((((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r ≤ _s)) (Litex.denote (Litex.neg _value_i21 (Litex.naturalToComplex _value_i21 h_4035))) (Litex.denote (Litex.neg _value_i20 (Litex.naturalToComplex _value_i20 (Litex.inNPos_natural _value_i20 h_3959))))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r ≤ _s)) _unfold_value (Litex.denote (Litex.neg _value_i20 (Litex.naturalToComplex _value_i20 (Litex.inNPos_natural _value_i20 h_3959))))) ((let _equal_wd_1_0 := _atomic_wd_2_0;
                      let _equal_wd_1_1 := (Litex.neg _value_i21 (Litex.naturalToComplex _value_i21 h_4035));
                      (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i17 (M := M))) (Litex.denote _value_i21)) = (M.negValue (Litex.denote _value_i21)) from by
                        have _litex_residual : (M.negValue (Litex.denote _value_i21)) = (M.negValue (Litex.denote _value_i21)) := (show @Eq M.Value _ _ from Eq.refl _)
                        exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i17 (M := M))) (Litex.denote _value_i21)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i17 (M := M))) (Litex.denote _value_i21)) = (M.negValue (Litex.denote _value_i21)) from by
                        let _litex_original := _equal_wd_1_0
                        let _litex_literal := (let _wd_1_0 := (_object_i17 (M := M));
                      let _wd_1_1 := _value_i21;
                      (let _litex_call_arg_0 := _wd_1_1;
                      Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) h_3963 True.intro))
                        have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_3939 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                        have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                        exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => (M.negValue _raw_i18)) _litex_input) (Litex.denote _litex_literal.val.argument) = (M.negValue (Litex.denote _value_i21)); exact rfl))
                      ))).trans _litex_residual)))).symm))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r ≤ _s)) (Litex.denote _atomic_wd_2_0) _unfold_value) ((let _equal_wd_1_0 := _atomic_wd_2_1;
                      let _equal_wd_1_1 := (Litex.neg _value_i20 (Litex.naturalToComplex _value_i20 (Litex.inNPos_natural _value_i20 h_3959)));
                      (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i17 (M := M))) (Litex.denote _value_i20)) = (M.negValue (Litex.denote _value_i20)) from by
                        have _litex_residual : (M.negValue (Litex.denote _value_i20)) = (M.negValue (Litex.denote _value_i20)) := (show @Eq M.Value _ _ from Eq.refl _)
                        exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i17 (M := M))) (Litex.denote _value_i20)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i17 (M := M))) (Litex.denote _value_i20)) = (M.negValue (Litex.denote _value_i20)) from by
                        let _litex_original := _equal_wd_1_0
                        let _litex_literal := (let _wd_1_0 := (_object_i17 (M := M));
                      let _wd_1_1 := _value_i20;
                      (let _litex_call_arg_0 := _wd_1_1;
                      Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) h_3959 True.intro))
                        have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_3939 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                        have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                        exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => (M.negValue _raw_i18)) _litex_input) (Litex.denote _litex_literal.val.argument) = (M.negValue (Litex.denote _value_i20)); exact rfl))
                      ))).trans _litex_residual)))).symm)) _unfold_child
                      ))
                  )
              )
            exact h_3942
          ))))
      )
  )

theorem h_11525 : ∀ {_Host_i24 : Type _} [_rep_i24 : Litex.Representation M _Host_i24] (_value_i24 : Litex.Obj (M := M) _Host_i24) (_member_i24 : Litex.In _value_i24 (Litex.NPos (M := M))) {_Host_i25 : Type _} [_rep_i25 : Litex.Representation M _Host_i25] (_value_i25 : Litex.Obj (M := M) _Host_i25) (_member_i25 : Litex.In _value_i25 (Litex.NPos (M := M))) (h_11523 : (∃ (_r _s : ℝ), (Litex.denote _value_i24) = M.number (_r : ℂ) ∧ (Litex.denote _value_i25) = M.number (_s : ℂ) ∧ _r ≤ _s)), (∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i17 (M := M))) (Litex.denote _value_i25)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i17 (M := M))) (Litex.denote _value_i24)) = M.number (_s : ℂ) ∧ _r ≤ _s) :=
  (by
    litex_complete =>
      exact (
        (fun {_Host_i24 : Type _} [_rep_i24 : Litex.Representation M _Host_i24] (_value_i24 : Litex.Obj (M := M) _Host_i24) (_member_i24 : Litex.In _value_i24 (Litex.NPos (M := M))) {_Host_i25 : Type _} [_rep_i25 : Litex.Representation M _Host_i25] (_value_i25 : Litex.Obj (M := M) _Host_i25) (_member_i25 : Litex.In _value_i25 (Litex.NPos (M := M))) (h_11523 : (∃ (_r _s : ℝ), (Litex.denote _value_i24) = M.number (_r : ℂ) ∧ (Litex.denote _value_i25) = M.number (_s : ℂ) ∧ _r ≤ _s)) => ((h_3940 (M := M))) (Litex.denote _value_i24) _member_i24 (Litex.denote _value_i25) _member_i25 h_11523)
      )
  )

theorem h_11526 : (by
  have _sequence_domain : Litex.In (_object_i17 (M := M)) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => True) _litex_input))) := (Litex.inOfSame (_object_i17 (M := M)) (_object_i17 (M := M)) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => True) _litex_input))) ((h_3939 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i17 (M := M))))
  exact Litex.SequenceStrictlyDecreasing (_object_i17 (M := M))) :=
  (by
    litex_complete =>
      exact (
        (by
          have _sequence_domain : Litex.In (_object_i17 (M := M)) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => True) _litex_input))) := (Litex.inOfSame (_object_i17 (M := M)) (_object_i17 (M := M)) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => True) _litex_input))) (Litex.fnSet (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.NPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => True) _litex_input))) ((h_3939 (M := M))).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet (_object_i17 (M := M))))
          exact (Litex.sequenceOrderOfForall true true (_object_i17 (M := M)) (show ∀ {_Host_i27 : Type _} [_rep_i27 : Litex.Representation M _Host_i27] (_value_i27 : Litex.Obj (M := M) _Host_i27) (h_11546 : Litex.In _value_i27 (Litex.NPos (M := M))) {_Host_i28 : Type _} [_rep_i28 : Litex.Representation M _Host_i28] (_value_i28 : Litex.Obj (M := M) _Host_i28) (h_11550 : Litex.In _value_i28 (Litex.NPos (M := M))) (h_11527 : Litex.Lt _value_i27 _value_i28), (by
            let _object_w29 := (let _litex_call_arg_0 := _value_i28;
            Litex.callOn ((_object_i17 (M := M))).val.signature (_object_i17 (M := M)) _litex_call_arg_0 (h_3938 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_11550, True.intro⟩))
            let _object_w30 := (let _litex_call_arg_0 := _value_i27;
            Litex.callOn ((_object_i17 (M := M))).val.signature (_object_i17 (M := M)) _litex_call_arg_0 (h_3938 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_11546, True.intro⟩))
            exact (by
              let _atomic_wd_2_0 := _object_w29
              let _atomic_wd_2_1 := _object_w30
              exact Litex.Lt _atomic_wd_2_0 _atomic_wd_2_1)
          ) from (by
            intro _Host_i27 _rep_i27 _value_i27 h_11546 _Host_i28 _rep_i28 _value_i28 h_11550 h_11527
            have h_11547 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i27 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inNPos_positive _value_i27 h_11546)
                  )
              )
            have h_11548 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i27 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.ltToLe (Litex.number (M := M) 0) _value_i27 h_11547)
                  )
              )
            have h_11549 : ¬ Litex.Same _value_i27 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i27 h_11547) _litex_zero.symm)
                  )
              )
            have h_11551 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i28 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inNPos_positive _value_i28 h_11550)
                  )
              )
            have h_11552 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i28 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.ltToLe (Litex.number (M := M) 0) _value_i28 h_11551)
                  )
              )
            have h_11553 : ¬ Litex.Same _value_i28 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i28 h_11551) _litex_zero.symm)
                  )
              )
            have h_11627 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i28 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.leLtTrans (Litex.number (M := M) (0 : ℂ)) _value_i27 _value_i28 h_11548 h_11527)
                  )
              )
            let _object_w29 := (let _litex_call_arg_0 := _value_i28;
            Litex.callOn ((_object_i17 (M := M))).val.signature (_object_i17 (M := M)) _litex_call_arg_0 (h_3938 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_11550, True.intro⟩))
            let _object_w30 := (let _litex_call_arg_0 := _value_i27;
            Litex.callOn ((_object_i17 (M := M))).val.signature (_object_i17 (M := M)) _litex_call_arg_0 (h_3938 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_11546, True.intro⟩))
            have h_11528 : (by
              let _atomic_wd_2_0 := _object_w29
              let _atomic_wd_2_1 := _object_w30
              exact Litex.Lt _atomic_wd_2_0 _atomic_wd_2_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (by
                      let _atomic_wd_2_0 := _object_w29
                      let _atomic_wd_2_1 := _object_w30
                      exact (by
                        change (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.denote _atomic_wd_2_0) (Litex.denote _atomic_wd_2_1)
                        have _unfold_child : (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.denote (Litex.neg _value_i28 (Litex.naturalToComplex _value_i28 (Litex.inNPos_natural _value_i28 h_11550)))) (Litex.denote (Litex.neg _value_i27 (Litex.naturalToComplex _value_i27 (Litex.inNPos_natural _value_i27 h_11546)))) := (by
                        let _atomic_wd_3_0 := (Litex.neg _value_i28 (Litex.naturalToComplex _value_i28 (Litex.inNPos_natural _value_i28 h_11550)))
                        let _atomic_wd_3_1 := (Litex.neg _value_i27 (Litex.naturalToComplex _value_i27 (Litex.inNPos_natural _value_i27 h_11546)))
                        exact (Litex.negationStrictOrder _atomic_wd_3_0 _atomic_wd_3_1 h_11527))
                        exact Eq.mp (((((Eq.refl ((fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.denote (Litex.neg _value_i28 (Litex.naturalToComplex _value_i28 (Litex.inNPos_natural _value_i28 h_11550)))) (Litex.denote (Litex.neg _value_i27 (Litex.naturalToComplex _value_i27 (Litex.inNPos_natural _value_i27 h_11546))))))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r < _s)) _unfold_value (Litex.denote (Litex.neg _value_i27 (Litex.naturalToComplex _value_i27 (Litex.inNPos_natural _value_i27 h_11546))))) ((let _equal_wd_1_0 := _atomic_wd_2_0;
                      let _equal_wd_1_1 := (Litex.neg _value_i28 (Litex.naturalToComplex _value_i28 (Litex.inNPos_natural _value_i28 h_11550)));
                      (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i17 (M := M))) (Litex.denote _value_i28)) = (M.negValue (Litex.denote _value_i28)) from by
                        have _litex_residual : (M.negValue (Litex.denote _value_i28)) = (M.negValue (Litex.denote _value_i28)) := (show @Eq M.Value _ _ from Eq.refl _)
                        exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i17 (M := M))) (Litex.denote _value_i28)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i17 (M := M))) (Litex.denote _value_i28)) = (M.negValue (Litex.denote _value_i28)) from by
                        let _litex_original := _equal_wd_1_0
                        let _litex_literal := (let _wd_1_0 := (_object_i17 (M := M));
                      let _wd_1_1 := _value_i28;
                      (let _litex_call_arg_0 := _wd_1_1;
                      Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) h_11550 True.intro))
                        have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_3939 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                        have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                        exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => (M.negValue _raw_i18)) _litex_input) (Litex.denote _litex_literal.val.argument) = (M.negValue (Litex.denote _value_i28)); exact rfl))
                      ))).trans _litex_residual)))).symm))).trans (congrArg (fun (_unfold_value : M.Value) => (fun (_unfold_arg0 : M.Value) (_unfold_arg1 : M.Value) => (∃ (_r _s : ℝ), _unfold_arg0 = M.number (_r : ℂ) ∧ _unfold_arg1 = M.number (_s : ℂ) ∧ _r < _s)) (Litex.denote _atomic_wd_2_0) _unfold_value) ((let _equal_wd_1_0 := _atomic_wd_2_1;
                      let _equal_wd_1_1 := (Litex.neg _value_i27 (Litex.naturalToComplex _value_i27 (Litex.inNPos_natural _value_i27 h_11546)));
                      (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i17 (M := M))) (Litex.denote _value_i27)) = (M.negValue (Litex.denote _value_i27)) from by
                        have _litex_residual : (M.negValue (Litex.denote _value_i27)) = (M.negValue (Litex.denote _value_i27)) := (show @Eq M.Value _ _ from Eq.refl _)
                        exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i17 (M := M))) (Litex.denote _value_i27)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i17 (M := M))) (Litex.denote _value_i27)) = (M.negValue (Litex.denote _value_i27)) from by
                        let _litex_original := _equal_wd_1_0
                        let _litex_literal := (let _wd_1_0 := (_object_i17 (M := M));
                      let _wd_1_1 := _value_i27;
                      (let _litex_call_arg_0 := _wd_1_1;
                      Litex.callOnDomain (Litex.NPos (M := M)) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) h_11546 True.intro))
                        have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_3939 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                        have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                        exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i18 : M.Value) => (M.negValue _raw_i18)) _litex_input) (Litex.denote _litex_literal.val.argument) = (M.negValue (Litex.denote _value_i27)); exact rfl))
                      ))).trans _litex_residual)))).symm)) _unfold_child
                      ))
                  )
              )
            exact h_11528
          ))))
      )
  )

theorem h_15307 : ∀ {_Host_i31 : Type _} [_rep_i31 : Litex.Representation M _Host_i31] (_value_i31 : Litex.Obj (M := M) _Host_i31) (_member_i31 : Litex.In _value_i31 (Litex.NPos (M := M))) {_Host_i32 : Type _} [_rep_i32 : Litex.Representation M _Host_i32] (_value_i32 : Litex.Obj (M := M) _Host_i32) (_member_i32 : Litex.In _value_i32 (Litex.NPos (M := M))) (h_15305 : (∃ (_r _s : ℝ), (Litex.denote _value_i31) = M.number (_r : ℂ) ∧ (Litex.denote _value_i32) = M.number (_s : ℂ) ∧ _r < _s)), (∃ (_r _s : ℝ), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i17 (M := M))) (Litex.denote _value_i32)) = M.number (_r : ℂ) ∧ (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i17 (M := M))) (Litex.denote _value_i31)) = M.number (_s : ℂ) ∧ _r < _s) :=
  (by
    litex_complete =>
      exact (
        (fun {_Host_i31 : Type _} [_rep_i31 : Litex.Representation M _Host_i31] (_value_i31 : Litex.Obj (M := M) _Host_i31) (_member_i31 : Litex.In _value_i31 (Litex.NPos (M := M))) {_Host_i32 : Type _} [_rep_i32 : Litex.Representation M _Host_i32] (_value_i32 : Litex.Obj (M := M) _Host_i32) (_member_i32 : Litex.In _value_i32 (Litex.NPos (M := M))) (h_15305 : (∃ (_r _s : ℝ), (Litex.denote _value_i31) = M.number (_r : ℂ) ∧ (Litex.denote _value_i32) = M.number (_s : ℂ) ∧ _r < _s)) => ((h_11526 (M := M))) (Litex.denote _value_i31) _member_i31 (Litex.denote _value_i32) _member_i32 h_15305)
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_sequence_x5f_monotonicity_x2f_statement_x2e_lit
