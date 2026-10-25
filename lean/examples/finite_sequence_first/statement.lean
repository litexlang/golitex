import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_sequence_x5f_first_x2f_statement_x2e_lit

universe u v5
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFnOn (let _litex_output := (Litex.R (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.denote _litex_output) (Litex.isSet (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) _raw_i2 (M.number (1 : ℂ)))) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → M.mem ((fun (_raw_i2 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) _raw_i2 (M.number (1 : ℂ)))) _raw_i2) (Litex.denote (Litex.R (M := M))) := (by
    intro _raw_i2 h_28 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_28)
    have h_28 : Litex.In _value_i2 (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))) := h_28
    let _object_h29 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))))
    have h_29 : Litex.In _value_i2 _object_h29 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inOfSame _value_i2 _value_i2 (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))) _object_h29 (Litex.sameRefl _value_i2) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) h_28)
          )
      )
    change (by
      let _atomic_wd_1_0 := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
      Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_29 (by
        let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
        exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro)
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
      Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_29 (by
        let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
        exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro)
      exact (by
        let _litex_return_call := _atomic_wd_1_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callOnInOutput _litex_return_call))))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard))
theorem h_116 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_117 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem h_119 : ∀ {_Host_i5 : Type v5} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_160 : Litex.In _value_i5 (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))), (by
  let _object_h161 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))))
  have h_161 : Litex.In _value_i5 _object_h161 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i5 _value_i5 (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))) _object_h161 (Litex.sameRefl _value_i5) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) h_160)
        )
    )
  let _object_w9 := (let _litex_call_arg_0 := _value_i5;
  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_116 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(by
    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
    exact h_160), True.intro⟩))
  let _object_w10 := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
  Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _value_i5 _litex_call_arg_0 h_161 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro)
  exact (by
    let _equal_wd_1_0 := _object_w9
    let _equal_wd_1_1 := _object_w10
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i5 _rep_i5 _value_i5 h_160
          let _object_h161 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))))
          have h_161 : Litex.In _value_i5 _object_h161 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i5 _value_i5 (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))) _object_h161 (Litex.sameRefl _value_i5) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) h_160)
                )
            )
          let _object_w9 := (let _litex_call_arg_0 := _value_i5;
          Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_116 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(by
            let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
            exact h_160), True.intro⟩))
          let _object_w10 := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _value_i5 _litex_call_arg_0 h_161 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro)
          have h_118 : (by
            let _equal_wd_1_0 := _object_w9
            let _equal_wd_1_1 := _object_w10
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w9;
                  let _equal_wd_1_1 := _object_w10;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i5)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (M.number (1 : ℂ))) from by
                    have _litex_residual : (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (M.number (1 : ℂ))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (M.number (1 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i5)))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i5)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (M.number (1 : ℂ))) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                  let _wd_1_1 := _value_i5;
                  (let _litex_call_arg_0 := _wd_1_1;
                  Litex.callOnDomain (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) (by
                    let _atomic_wd_1_1 := (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
                    exact h_160) True.intro))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_117 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) _raw_i2 (M.number (1 : ℂ)))) _litex_input) (Litex.denote _litex_literal.val.argument) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i5) (M.number (1 : ℂ))); exact rfl))
                  ))).trans _litex_residual)))
                )
            )
          exact h_118
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_finite_x5f_sequence_x5f_first_x2f_statement_x2e_lit
