import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_signed_x5f_numeric_x5f_identity_x5f_functions_x2f_statement_x2e_lit

universe u v3 v6 v9 v12 v15 v18 v21 v24
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFnOn (let _litex_output := (Litex.QPos (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.QPos (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.QPos (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => _raw_i2) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.QPos (M := M))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → M.mem ((fun (_raw_i2 : M.Value) => _raw_i2) _raw_i2) (Litex.denote (Litex.QPos (M := M))) := (by
    intro _raw_i2 h_14 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
    have h_14 : Litex.In _value_i2 (Litex.QPos (M := M)) := h_14
    have h_15 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i2 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inQPos_positive _value_i2 h_14)
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
    change Litex.In _value_i2 (Litex.QPos (M := M))
    exact h_14)
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.QPos (M := M))) (Litex.denote (Litex.QPos (M := M))) (Litex.isSet (Litex.QPos (M := M))) (Litex.isSet (Litex.QPos (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard))
theorem h_27 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_28 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem h_30 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_43 : Litex.In _value_i3 (Litex.QPos (M := M))), (by
  let _object_w9 := (let _wd_1_0 := (let _litex_call_arg_0 := _value_i3;
  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_27 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_43, True.intro⟩));
  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.rationalToComplex _atomic_wd_1_0 (Litex.inQPos_base _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))) (Litex.numberInC (M := M) (0 : ℂ))))
  let _object_w10 := (let _litex_call_arg_0 := _value_i3;
  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_27 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_43, True.intro⟩))
  exact (by
    let _equal_wd_1_0 := _object_w9
    let _equal_wd_1_1 := _object_w10
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_43
          have h_44 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQPos_positive _value_i3 h_43)
                )
            )
          have h_45 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe (Litex.number (M := M) 0) _value_i3 h_44)
                )
            )
          have h_46 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i3 h_44) _litex_zero.symm)
                )
            )
          let _object_w9 := (let _wd_1_0 := (let _litex_call_arg_0 := _value_i3;
          Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_27 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_43, True.intro⟩));
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.rationalToComplex _atomic_wd_1_0 (Litex.inQPos_base _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))) (Litex.numberInC (M := M) (0 : ℂ))))
          let _object_w10 := (let _litex_call_arg_0 := _value_i3;
          Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_27 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_43, True.intro⟩))
          have h_29 : (by
            let _equal_wd_1_0 := _object_w9
            let _equal_wd_1_1 := _object_w10
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w9;
                  let _equal_wd_1_1 := _object_w10;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((let _litex_numeric_call := (_equal_wd_1_0).val.left;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.rationalToComplex _litex_numeric_call (Litex.inQPos_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.QPos (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) + (0 : ℂ)) (let _litex_numeric_call := _equal_wd_1_1;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.rationalToComplex _litex_numeric_call (Litex.inQPos_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.QPos (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) (Litex.NativeBridge.denoteAdd (_equal_wd_1_0).val.left (Litex.number (M := M) (0 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (let _litex_numeric_call := (_equal_wd_1_0).val.left;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.rationalToComplex _litex_numeric_call (Litex.inQPos_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.QPos (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (let _litex_numeric_call := _equal_wd_1_1;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.rationalToComplex _litex_numeric_call (Litex.inQPos_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.QPos (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (by ring!))))
                )
            )
          exact h_29
        )
      )
  )

noncomputable def _object_i4 := (Litex.formulaFnOn (let _litex_output := (Litex.QNeg (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.QNeg (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.QNeg (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => _raw_i5) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote (Litex.QNeg (M := M))) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → M.mem ((fun (_raw_i5 : M.Value) => _raw_i5) _raw_i5) (Litex.denote (Litex.QNeg (M := M))) := (by
    intro _raw_i5 h_140 _
    let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_140)
    have h_140 : Litex.In _value_i5 (Litex.QNeg (M := M)) := h_140
    have h_141 : Litex.Lt _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inQNeg_negative _value_i5 h_140)
          )
      )
    have h_142 : Litex.Le _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe _value_i5 (Litex.number (M := M) 0) h_141)
          )
      )
    have h_143 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltNotSame _value_i5 (Litex.number (M := M) 0) h_141)
          )
      )
    change Litex.In _value_i5 (Litex.QNeg (M := M))
    exact h_140)
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.QNeg (M := M))) (Litex.denote (Litex.QNeg (M := M))) (Litex.isSet (Litex.QNeg (M := M))) (Litex.isSet (Litex.QNeg (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard))
theorem h_153 : Litex.In (_object_i4 (M := M)) (Litex.fnSet ((_object_i4 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i4 (M := M)))
      )
  )
theorem h_154 : Litex.Same (_object_i4 (M := M)) (_object_i4 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i4 (M := M)))
      )
  )

theorem h_156 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_169 : Litex.In _value_i6 (Litex.QNeg (M := M))), (by
  let _object_w19 := (let _wd_1_0 := (let _litex_call_arg_0 := _value_i6;
  Litex.callOn ((_object_i4 (M := M))).val.signature (_object_i4 (M := M)) _litex_call_arg_0 (h_153 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_169, True.intro⟩));
  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.rationalToComplex _atomic_wd_1_0 (Litex.inQNeg_base _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))) (Litex.numberInC (M := M) (0 : ℂ))))
  let _object_w20 := (let _litex_call_arg_0 := _value_i6;
  Litex.callOn ((_object_i4 (M := M))).val.signature (_object_i4 (M := M)) _litex_call_arg_0 (h_153 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_169, True.intro⟩))
  exact (by
    let _equal_wd_1_0 := _object_w19
    let _equal_wd_1_1 := _object_w20
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_169
          have h_170 : Litex.Lt _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQNeg_negative _value_i6 h_169)
                )
            )
          have h_171 : Litex.Le _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe _value_i6 (Litex.number (M := M) 0) h_170)
                )
            )
          have h_172 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltNotSame _value_i6 (Litex.number (M := M) 0) h_170)
                )
            )
          let _object_w19 := (let _wd_1_0 := (let _litex_call_arg_0 := _value_i6;
          Litex.callOn ((_object_i4 (M := M))).val.signature (_object_i4 (M := M)) _litex_call_arg_0 (h_153 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_169, True.intro⟩));
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.rationalToComplex _atomic_wd_1_0 (Litex.inQNeg_base _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))) (Litex.numberInC (M := M) (0 : ℂ))))
          let _object_w20 := (let _litex_call_arg_0 := _value_i6;
          Litex.callOn ((_object_i4 (M := M))).val.signature (_object_i4 (M := M)) _litex_call_arg_0 (h_153 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_169, True.intro⟩))
          have h_155 : (by
            let _equal_wd_1_0 := _object_w19
            let _equal_wd_1_1 := _object_w20
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w19;
                  let _equal_wd_1_1 := _object_w20;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((let _litex_numeric_call := (_equal_wd_1_0).val.left;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.rationalToComplex _litex_numeric_call (Litex.inQNeg_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.QNeg (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) + (0 : ℂ)) (let _litex_numeric_call := _equal_wd_1_1;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.rationalToComplex _litex_numeric_call (Litex.inQNeg_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.QNeg (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) (Litex.NativeBridge.denoteAdd (_equal_wd_1_0).val.left (Litex.number (M := M) (0 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (let _litex_numeric_call := (_equal_wd_1_0).val.left;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.rationalToComplex _litex_numeric_call (Litex.inQNeg_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.QNeg (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (let _litex_numeric_call := _equal_wd_1_1;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.rationalToComplex _litex_numeric_call (Litex.inQNeg_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.QNeg (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (by ring!))))
                )
            )
          exact h_155
        )
      )
  )

noncomputable def _object_i7 := (Litex.formulaFnOn (let _litex_output := (Litex.ZNeg (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.ZNeg (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.ZNeg (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => _raw_i8) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i8 : M.Value), M.mem _raw_i8 (Litex.denote (Litex.ZNeg (M := M))) → ((fun (_raw_i8 : M.Value) => True) _raw_i8) → M.mem ((fun (_raw_i8 : M.Value) => _raw_i8) _raw_i8) (Litex.denote (Litex.ZNeg (M := M))) := (by
    intro _raw_i8 h_288 _
    let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_288)
    have h_288 : Litex.In _value_i8 (Litex.ZNeg (M := M)) := h_288
    have h_289 : Litex.Lt _value_i8 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inZNeg_negative _value_i8 h_288)
          )
      )
    have h_290 : Litex.Le _value_i8 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe _value_i8 (Litex.number (M := M) 0) h_289)
          )
      )
    have h_291 : ¬ Litex.Same _value_i8 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltNotSame _value_i8 (Litex.number (M := M) 0) h_289)
          )
      )
    change Litex.In _value_i8 (Litex.ZNeg (M := M))
    exact h_288)
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.ZNeg (M := M))) (Litex.denote (Litex.ZNeg (M := M))) (Litex.isSet (Litex.ZNeg (M := M))) (Litex.isSet (Litex.ZNeg (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i8 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard))
theorem h_301 : Litex.In (_object_i7 (M := M)) (Litex.fnSet ((_object_i7 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i7 (M := M)))
      )
  )
theorem h_302 : Litex.Same (_object_i7 (M := M)) (_object_i7 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i7 (M := M)))
      )
  )

theorem h_304 : ∀ {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_317 : Litex.In _value_i9 (Litex.ZNeg (M := M))), (by
  let _object_w29 := (let _wd_1_0 := (let _litex_call_arg_0 := _value_i9;
  Litex.callOn ((_object_i7 (M := M))).val.signature (_object_i7 (M := M)) _litex_call_arg_0 (h_301 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_317, True.intro⟩));
  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.inZNeg_base _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))) (Litex.numberInC (M := M) (0 : ℂ))))
  let _object_w30 := (let _litex_call_arg_0 := _value_i9;
  Litex.callOn ((_object_i7 (M := M))).val.signature (_object_i7 (M := M)) _litex_call_arg_0 (h_301 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_317, True.intro⟩))
  exact (by
    let _equal_wd_1_0 := _object_w29
    let _equal_wd_1_1 := _object_w30
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i9 _rep_i9 _value_i9 h_317
          have h_318 : Litex.Lt _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inZNeg_negative _value_i9 h_317)
                )
            )
          have h_319 : Litex.Le _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe _value_i9 (Litex.number (M := M) 0) h_318)
                )
            )
          have h_320 : ¬ Litex.Same _value_i9 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltNotSame _value_i9 (Litex.number (M := M) 0) h_318)
                )
            )
          let _object_w29 := (let _wd_1_0 := (let _litex_call_arg_0 := _value_i9;
          Litex.callOn ((_object_i7 (M := M))).val.signature (_object_i7 (M := M)) _litex_call_arg_0 (h_301 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_317, True.intro⟩));
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.inZNeg_base _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))) (Litex.numberInC (M := M) (0 : ℂ))))
          let _object_w30 := (let _litex_call_arg_0 := _value_i9;
          Litex.callOn ((_object_i7 (M := M))).val.signature (_object_i7 (M := M)) _litex_call_arg_0 (h_301 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_317, True.intro⟩))
          have h_303 : (by
            let _equal_wd_1_0 := _object_w29
            let _equal_wd_1_1 := _object_w30
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w29;
                  let _equal_wd_1_1 := _object_w30;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((let _litex_numeric_call := (_equal_wd_1_0).val.left;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.integerToComplex _litex_numeric_call (Litex.inZNeg_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.ZNeg (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) + (0 : ℂ)) (let _litex_numeric_call := _equal_wd_1_1;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.integerToComplex _litex_numeric_call (Litex.inZNeg_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.ZNeg (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) (Litex.NativeBridge.denoteAdd (_equal_wd_1_0).val.left (Litex.number (M := M) (0 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (let _litex_numeric_call := (_equal_wd_1_0).val.left;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.integerToComplex _litex_numeric_call (Litex.inZNeg_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.ZNeg (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (let _litex_numeric_call := _equal_wd_1_1;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.integerToComplex _litex_numeric_call (Litex.inZNeg_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.ZNeg (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (by ring!))))
                )
            )
          exact h_303
        )
      )
  )

noncomputable def _object_i10 := (Litex.formulaFnOn (let _litex_output := (Litex.RNeg (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.RNeg (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.RNeg (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => _raw_i11) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i11 : M.Value), M.mem _raw_i11 (Litex.denote (Litex.RNeg (M := M))) → ((fun (_raw_i11 : M.Value) => True) _raw_i11) → M.mem ((fun (_raw_i11 : M.Value) => _raw_i11) _raw_i11) (Litex.denote (Litex.RNeg (M := M))) := (by
    intro _raw_i11 h_458 _
    let _value_i11 := Litex.semanticObject (M := M) _raw_i11 (M.member_isSet h_458)
    have h_458 : Litex.In _value_i11 (Litex.RNeg (M := M)) := h_458
    have h_459 : Litex.Lt _value_i11 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRNeg_negative _value_i11 h_458)
          )
      )
    have h_460 : Litex.Le _value_i11 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe _value_i11 (Litex.number (M := M) 0) h_459)
          )
      )
    have h_461 : ¬ Litex.Same _value_i11 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltNotSame _value_i11 (Litex.number (M := M) 0) h_459)
          )
      )
    change Litex.In _value_i11 (Litex.RNeg (M := M))
    exact h_458)
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.RNeg (M := M))) (Litex.denote (Litex.RNeg (M := M))) (Litex.isSet (Litex.RNeg (M := M))) (Litex.isSet (Litex.RNeg (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard))
theorem h_471 : Litex.In (_object_i10 (M := M)) (Litex.fnSet ((_object_i10 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i10 (M := M)))
      )
  )
theorem h_472 : Litex.Same (_object_i10 (M := M)) (_object_i10 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i10 (M := M)))
      )
  )

theorem h_474 : ∀ {_Host_i12 : Type v12} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_487 : Litex.In _value_i12 (Litex.RNeg (M := M))), (by
  let _object_w39 := (let _wd_1_0 := (let _litex_call_arg_0 := _value_i12;
  Litex.callOn ((_object_i10 (M := M))).val.signature (_object_i10 (M := M)) _litex_call_arg_0 (h_471 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_487, True.intro⟩));
  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.inRNeg_base _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))) (Litex.numberInC (M := M) (0 : ℂ))))
  let _object_w40 := (let _litex_call_arg_0 := _value_i12;
  Litex.callOn ((_object_i10 (M := M))).val.signature (_object_i10 (M := M)) _litex_call_arg_0 (h_471 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_487, True.intro⟩))
  exact (by
    let _equal_wd_1_0 := _object_w39
    let _equal_wd_1_1 := _object_w40
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i12 _rep_i12 _value_i12 h_487
          have h_488 : Litex.Lt _value_i12 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRNeg_negative _value_i12 h_487)
                )
            )
          have h_489 : Litex.Le _value_i12 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltToLe _value_i12 (Litex.number (M := M) 0) h_488)
                )
            )
          have h_490 : ¬ Litex.Same _value_i12 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.ltNotSame _value_i12 (Litex.number (M := M) 0) h_488)
                )
            )
          let _object_w39 := (let _wd_1_0 := (let _litex_call_arg_0 := _value_i12;
          Litex.callOn ((_object_i10 (M := M))).val.signature (_object_i10 (M := M)) _litex_call_arg_0 (h_471 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_487, True.intro⟩));
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.realToComplex _atomic_wd_1_0 (Litex.inRNeg_base _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))) (Litex.numberInC (M := M) (0 : ℂ))))
          let _object_w40 := (let _litex_call_arg_0 := _value_i12;
          Litex.callOn ((_object_i10 (M := M))).val.signature (_object_i10 (M := M)) _litex_call_arg_0 (h_471 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_487, True.intro⟩))
          have h_473 : (by
            let _equal_wd_1_0 := _object_w39
            let _equal_wd_1_1 := _object_w40
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w39;
                  let _equal_wd_1_1 := _object_w40;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((let _litex_numeric_call := (_equal_wd_1_0).val.left;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (Litex.inRNeg_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.RNeg (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) + (0 : ℂ)) (let _litex_numeric_call := _equal_wd_1_1;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (Litex.inRNeg_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.RNeg (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) (Litex.NativeBridge.denoteAdd (_equal_wd_1_0).val.left (Litex.number (M := M) (0 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (let _litex_numeric_call := (_equal_wd_1_0).val.left;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (Litex.inRNeg_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.RNeg (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (let _litex_numeric_call := _equal_wd_1_1;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (Litex.inRNeg_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.RNeg (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (by ring!))))
                )
            )
          exact h_473
        )
      )
  )

noncomputable def _object_i13 := (Litex.formulaFnOn (let _litex_output := (Litex.QStar (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.QStar (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.QStar (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) => _raw_i14) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i14 : M.Value), M.mem _raw_i14 (Litex.denote (Litex.QStar (M := M))) → ((fun (_raw_i14 : M.Value) => True) _raw_i14) → M.mem ((fun (_raw_i14 : M.Value) => _raw_i14) _raw_i14) (Litex.denote (Litex.QStar (M := M))) := (by
    intro _raw_i14 h_650 _
    let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_650)
    have h_650 : Litex.In _value_i14 (Litex.QStar (M := M)) := h_650
    have h_651 : ¬ Litex.Same _value_i14 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inQStar_nonzero _value_i14 h_650)
          )
      )
    change Litex.In _value_i14 (Litex.QStar (M := M))
    exact h_650)
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.QStar (M := M))) (Litex.denote (Litex.QStar (M := M))) (Litex.isSet (Litex.QStar (M := M))) (Litex.isSet (Litex.QStar (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard))
theorem h_659 : Litex.In (_object_i13 (M := M)) (Litex.fnSet ((_object_i13 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i13 (M := M)))
      )
  )
theorem h_660 : Litex.Same (_object_i13 (M := M)) (_object_i13 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i13 (M := M)))
      )
  )

theorem h_662 : ∀ {_Host_i15 : Type v15} [_rep_i15 : Litex.Representation M _Host_i15] (_value_i15 : Litex.Obj (M := M) _Host_i15) (h_675 : Litex.In _value_i15 (Litex.QStar (M := M))), (by
  let _object_w49 := (let _wd_1_0 := (let _litex_call_arg_0 := _value_i15;
  Litex.callOn ((_object_i13 (M := M))).val.signature (_object_i13 (M := M)) _litex_call_arg_0 (h_659 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_675, True.intro⟩));
  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.rationalToComplex _atomic_wd_1_0 (Litex.inQStar_base _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))) (Litex.numberInC (M := M) (0 : ℂ))))
  let _object_w50 := (let _litex_call_arg_0 := _value_i15;
  Litex.callOn ((_object_i13 (M := M))).val.signature (_object_i13 (M := M)) _litex_call_arg_0 (h_659 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_675, True.intro⟩))
  exact (by
    let _equal_wd_1_0 := _object_w49
    let _equal_wd_1_1 := _object_w50
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i15 _rep_i15 _value_i15 h_675
          have h_676 : ¬ Litex.Same _value_i15 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQStar_nonzero _value_i15 h_675)
                )
            )
          let _object_w49 := (let _wd_1_0 := (let _litex_call_arg_0 := _value_i15;
          Litex.callOn ((_object_i13 (M := M))).val.signature (_object_i13 (M := M)) _litex_call_arg_0 (h_659 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_675, True.intro⟩));
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.rationalToComplex _atomic_wd_1_0 (Litex.inQStar_base _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))) (Litex.numberInC (M := M) (0 : ℂ))))
          let _object_w50 := (let _litex_call_arg_0 := _value_i15;
          Litex.callOn ((_object_i13 (M := M))).val.signature (_object_i13 (M := M)) _litex_call_arg_0 (h_659 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_675, True.intro⟩))
          have h_661 : (by
            let _equal_wd_1_0 := _object_w49
            let _equal_wd_1_1 := _object_w50
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w49;
                  let _equal_wd_1_1 := _object_w50;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((let _litex_numeric_call := (_equal_wd_1_0).val.left;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.rationalToComplex _litex_numeric_call (Litex.inQStar_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.QStar (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) + (0 : ℂ)) (let _litex_numeric_call := _equal_wd_1_1;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.rationalToComplex _litex_numeric_call (Litex.inQStar_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.QStar (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) (Litex.NativeBridge.denoteAdd (_equal_wd_1_0).val.left (Litex.number (M := M) (0 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (let _litex_numeric_call := (_equal_wd_1_0).val.left;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.rationalToComplex _litex_numeric_call (Litex.inQStar_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.QStar (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (let _litex_numeric_call := _equal_wd_1_1;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.rationalToComplex _litex_numeric_call (Litex.inQStar_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.QStar (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (by ring!))))
                )
            )
          exact h_661
        )
      )
  )

noncomputable def _object_i16 := (Litex.formulaFnOn (let _litex_output := (Litex.ZStar (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.ZStar (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.ZStar (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) => _raw_i17) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i17 : M.Value), M.mem _raw_i17 (Litex.denote (Litex.ZStar (M := M))) → ((fun (_raw_i17 : M.Value) => True) _raw_i17) → M.mem ((fun (_raw_i17 : M.Value) => _raw_i17) _raw_i17) (Litex.denote (Litex.ZStar (M := M))) := (by
    intro _raw_i17 h_858 _
    let _value_i17 := Litex.semanticObject (M := M) _raw_i17 (M.member_isSet h_858)
    have h_858 : Litex.In _value_i17 (Litex.ZStar (M := M)) := h_858
    have h_859 : ¬ Litex.Same _value_i17 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inZStar_nonzero _value_i17 h_858)
          )
      )
    change Litex.In _value_i17 (Litex.ZStar (M := M))
    exact h_858)
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.ZStar (M := M))) (Litex.denote (Litex.ZStar (M := M))) (Litex.isSet (Litex.ZStar (M := M))) (Litex.isSet (Litex.ZStar (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard))
theorem h_867 : Litex.In (_object_i16 (M := M)) (Litex.fnSet ((_object_i16 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i16 (M := M)))
      )
  )
theorem h_868 : Litex.Same (_object_i16 (M := M)) (_object_i16 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i16 (M := M)))
      )
  )

theorem h_870 : ∀ {_Host_i18 : Type v18} [_rep_i18 : Litex.Representation M _Host_i18] (_value_i18 : Litex.Obj (M := M) _Host_i18) (h_883 : Litex.In _value_i18 (Litex.ZStar (M := M))), (by
  let _object_w59 := (let _wd_1_0 := (let _litex_call_arg_0 := _value_i18;
  Litex.callOn ((_object_i16 (M := M))).val.signature (_object_i16 (M := M)) _litex_call_arg_0 (h_867 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_883, True.intro⟩));
  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.inZStar_base _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))) (Litex.numberInC (M := M) (0 : ℂ))))
  let _object_w60 := (let _litex_call_arg_0 := _value_i18;
  Litex.callOn ((_object_i16 (M := M))).val.signature (_object_i16 (M := M)) _litex_call_arg_0 (h_867 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_883, True.intro⟩))
  exact (by
    let _equal_wd_1_0 := _object_w59
    let _equal_wd_1_1 := _object_w60
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i18 _rep_i18 _value_i18 h_883
          have h_884 : ¬ Litex.Same _value_i18 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inZStar_nonzero _value_i18 h_883)
                )
            )
          let _object_w59 := (let _wd_1_0 := (let _litex_call_arg_0 := _value_i18;
          Litex.callOn ((_object_i16 (M := M))).val.signature (_object_i16 (M := M)) _litex_call_arg_0 (h_867 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_883, True.intro⟩));
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.integerToComplex _atomic_wd_1_0 (Litex.inZStar_base _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))) (Litex.numberInC (M := M) (0 : ℂ))))
          let _object_w60 := (let _litex_call_arg_0 := _value_i18;
          Litex.callOn ((_object_i16 (M := M))).val.signature (_object_i16 (M := M)) _litex_call_arg_0 (h_867 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_883, True.intro⟩))
          have h_869 : (by
            let _equal_wd_1_0 := _object_w59
            let _equal_wd_1_1 := _object_w60
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w59;
                  let _equal_wd_1_1 := _object_w60;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((let _litex_numeric_call := (_equal_wd_1_0).val.left;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.integerToComplex _litex_numeric_call (Litex.inZStar_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.ZStar (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) + (0 : ℂ)) (let _litex_numeric_call := _equal_wd_1_1;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.integerToComplex _litex_numeric_call (Litex.inZStar_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.ZStar (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) (Litex.NativeBridge.denoteAdd (_equal_wd_1_0).val.left (Litex.number (M := M) (0 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (let _litex_numeric_call := (_equal_wd_1_0).val.left;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.integerToComplex _litex_numeric_call (Litex.inZStar_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.ZStar (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (let _litex_numeric_call := _equal_wd_1_1;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.integerToComplex _litex_numeric_call (Litex.inZStar_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.ZStar (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (by ring!))))
                )
            )
          exact h_869
        )
      )
  )

noncomputable def _object_i19 := (Litex.formulaFnOn (let _litex_output := (Litex.RStar (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.RStar (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.RStar (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i20 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i20 : M.Value) => _raw_i20) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i20 : M.Value), M.mem _raw_i20 (Litex.denote (Litex.RStar (M := M))) → ((fun (_raw_i20 : M.Value) => True) _raw_i20) → M.mem ((fun (_raw_i20 : M.Value) => _raw_i20) _raw_i20) (Litex.denote (Litex.RStar (M := M))) := (by
    intro _raw_i20 h_1088 _
    let _value_i20 := Litex.semanticObject (M := M) _raw_i20 (M.member_isSet h_1088)
    have h_1088 : Litex.In _value_i20 (Litex.RStar (M := M)) := h_1088
    have h_1089 : ¬ Litex.Same _value_i20 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inRStar_nonzero _value_i20 h_1088)
          )
      )
    change Litex.In _value_i20 (Litex.RStar (M := M))
    exact h_1088)
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.RStar (M := M))) (Litex.denote (Litex.RStar (M := M))) (Litex.isSet (Litex.RStar (M := M))) (Litex.isSet (Litex.RStar (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i20 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard))
theorem h_1097 : Litex.In (_object_i19 (M := M)) (Litex.fnSet ((_object_i19 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i19 (M := M)))
      )
  )
theorem h_1098 : Litex.Same (_object_i19 (M := M)) (_object_i19 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i19 (M := M)))
      )
  )

theorem h_1100 : ∀ {_Host_i21 : Type v21} [_rep_i21 : Litex.Representation M _Host_i21] (_value_i21 : Litex.Obj (M := M) _Host_i21) (h_1113 : Litex.In _value_i21 (Litex.RStar (M := M))), (by
  let _object_w69 := (let _wd_1_0 := (let _litex_call_arg_0 := _value_i21;
  Litex.callOn ((_object_i19 (M := M))).val.signature (_object_i19 (M := M)) _litex_call_arg_0 (h_1097 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_1113, True.intro⟩));
  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.realToComplex _atomic_wd_1_0 (Litex.inRStar_base _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))) (Litex.numberInC (M := M) (0 : ℂ))))
  let _object_w70 := (let _litex_call_arg_0 := _value_i21;
  Litex.callOn ((_object_i19 (M := M))).val.signature (_object_i19 (M := M)) _litex_call_arg_0 (h_1097 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_1113, True.intro⟩))
  exact (by
    let _equal_wd_1_0 := _object_w69
    let _equal_wd_1_1 := _object_w70
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i21 _rep_i21 _value_i21 h_1113
          have h_1114 : ¬ Litex.Same _value_i21 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inRStar_nonzero _value_i21 h_1113)
                )
            )
          let _object_w69 := (let _wd_1_0 := (let _litex_call_arg_0 := _value_i21;
          Litex.callOn ((_object_i19 (M := M))).val.signature (_object_i19 (M := M)) _litex_call_arg_0 (h_1097 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_1113, True.intro⟩));
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.realToComplex _atomic_wd_1_0 (Litex.inRStar_base _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0)))) (Litex.numberInC (M := M) (0 : ℂ))))
          let _object_w70 := (let _litex_call_arg_0 := _value_i21;
          Litex.callOn ((_object_i19 (M := M))).val.signature (_object_i19 (M := M)) _litex_call_arg_0 (h_1097 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_1113, True.intro⟩))
          have h_1099 : (by
            let _equal_wd_1_0 := _object_w69
            let _equal_wd_1_1 := _object_w70
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w69;
                  let _equal_wd_1_1 := _object_w70;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((let _litex_numeric_call := (_equal_wd_1_0).val.left;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (Litex.inRStar_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.RStar (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) + (0 : ℂ)) (let _litex_numeric_call := _equal_wd_1_1;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (Litex.inRStar_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.RStar (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) (Litex.NativeBridge.denoteAdd (_equal_wd_1_0).val.left (Litex.number (M := M) (0 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (let _litex_numeric_call := (_equal_wd_1_0).val.left;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (Litex.inRStar_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.RStar (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (let _litex_numeric_call := _equal_wd_1_1;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.realToComplex _litex_numeric_call (Litex.inRStar_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.RStar (M := M)) from (Litex.callOnInOutput _litex_numeric_call))));
                  Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (by ring!))))
                )
            )
          exact h_1099
        )
      )
  )

noncomputable def _object_i22 := (Litex.formulaFnOn (let _litex_output := (Litex.CStar (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.CStar (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.CStar (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i23 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i23 : M.Value) => _raw_i23) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i23 : M.Value), M.mem _raw_i23 (Litex.denote (Litex.CStar (M := M))) → ((fun (_raw_i23 : M.Value) => True) _raw_i23) → M.mem ((fun (_raw_i23 : M.Value) => _raw_i23) _raw_i23) (Litex.denote (Litex.CStar (M := M))) := (by
    intro _raw_i23 h_1340 _
    let _value_i23 := Litex.semanticObject (M := M) _raw_i23 (M.member_isSet h_1340)
    have h_1340 : Litex.In _value_i23 (Litex.CStar (M := M)) := h_1340
    have h_1341 : ¬ Litex.Same _value_i23 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inCStar_nonzero _value_i23 h_1340)
          )
      )
    change Litex.In _value_i23 (Litex.CStar (M := M))
    exact h_1340)
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.CStar (M := M))) (Litex.denote (Litex.CStar (M := M))) (Litex.isSet (Litex.CStar (M := M))) (Litex.isSet (Litex.CStar (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i23 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard))
theorem h_1349 : Litex.In (_object_i22 (M := M)) (Litex.fnSet ((_object_i22 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i22 (M := M)))
      )
  )
theorem h_1350 : Litex.Same (_object_i22 (M := M)) (_object_i22 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i22 (M := M)))
      )
  )

theorem h_1352 : ∀ {_Host_i24 : Type v24} [_rep_i24 : Litex.Representation M _Host_i24] (_value_i24 : Litex.Obj (M := M) _Host_i24) (h_1365 : Litex.In _value_i24 (Litex.CStar (M := M))), (by
  let _object_w79 := (let _wd_1_0 := (let _litex_call_arg_0 := _value_i24;
  Litex.callOn ((_object_i22 (M := M))).val.signature (_object_i22 (M := M)) _litex_call_arg_0 (h_1349 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_1365, True.intro⟩));
  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (Litex.inCStar_base _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0))) (Litex.numberInC (M := M) (0 : ℂ))))
  let _object_w80 := (let _litex_call_arg_0 := _value_i24;
  Litex.callOn ((_object_i22 (M := M))).val.signature (_object_i22 (M := M)) _litex_call_arg_0 (h_1349 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_1365, True.intro⟩))
  exact (by
    let _equal_wd_1_0 := _object_w79
    let _equal_wd_1_1 := _object_w80
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i24 _rep_i24 _value_i24 h_1365
          have h_1366 : ¬ Litex.Same _value_i24 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inCStar_nonzero _value_i24 h_1365)
                )
            )
          let _object_w79 := (let _wd_1_0 := (let _litex_call_arg_0 := _value_i24;
          Litex.callOn ((_object_i22 (M := M))).val.signature (_object_i22 (M := M)) _litex_call_arg_0 (h_1349 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_1365, True.intro⟩));
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.inCStar_base _atomic_wd_1_0 (Litex.callOnInOutput _atomic_wd_1_0))) (Litex.numberInC (M := M) (0 : ℂ))))
          let _object_w80 := (let _litex_call_arg_0 := _value_i24;
          Litex.callOn ((_object_i22 (M := M))).val.signature (_object_i22 (M := M)) _litex_call_arg_0 (h_1349 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_1365, True.intro⟩))
          have h_1351 : (by
            let _equal_wd_1_0 := _object_w79
            let _equal_wd_1_1 := _object_w80
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w79;
                  let _equal_wd_1_1 := _object_w80;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((let _litex_numeric_call := (_equal_wd_1_0).val.left;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.inCStar_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.CStar (M := M)) from (Litex.callOnInOutput _litex_numeric_call)));
                  Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) + (0 : ℂ)) (let _litex_numeric_call := _equal_wd_1_1;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.inCStar_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.CStar (M := M)) from (Litex.callOnInOutput _litex_numeric_call)));
                  Litex.NativeBridge.asComplex _litex_numeric_call _litex_numeric_member) (Litex.NativeBridge.denoteAdd (_equal_wd_1_0).val.left (Litex.number (M := M) (0 : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (let _litex_numeric_call := (_equal_wd_1_0).val.left;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.inCStar_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.CStar (M := M)) from (Litex.callOnInOutput _litex_numeric_call)));
                  Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))) (let _litex_numeric_call := _equal_wd_1_1;
                  let _litex_numeric_member : Litex.In _litex_numeric_call Litex.C := (Litex.inCStar_base _litex_numeric_call (show Litex.In _litex_numeric_call (Litex.CStar (M := M)) from (Litex.callOnInOutput _litex_numeric_call)));
                  Litex.NativeBridge.asComplex_spec _litex_numeric_call _litex_numeric_member) (by ring!))))
                )
            )
          exact h_1351
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_signed_x5f_numeric_x5f_identity_x5f_functions_x2f_statement_x2e_lit
