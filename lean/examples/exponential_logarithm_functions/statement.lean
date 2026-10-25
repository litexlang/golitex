import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_exponential_x5f_logarithm_x5f_functions_x2f_statement_x2e_lit

universe u v1 v6
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_w1 := (Litex.add (Litex.number (M := M) (Real.pi : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (Litex.positiveRealToComplex (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)) (Litex.positiveRealToComplex (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)))

noncomputable def _object_w2 := (Litex.mul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.positiveRealToComplex (Litex.number (M := M) (Real.pi : ℂ)) (show Litex.In (Litex.number (M := M) (Real.pi : ℂ)) (Litex.RPos (M := M)) from Litex.numberInRPos Real.pi Real.pi_pos)))

theorem h_1 : (by
  let _equal_wd_1_0 := (_object_w1 (M := M))
  let _equal_wd_1_1 := (_object_w2 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w1 (M := M));
        let _equal_wd_1_1 := (_object_w2 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Real.pi : ℂ) + (Real.pi : ℂ)) ((2 : ℂ) * (Real.pi : ℂ)) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (Real.pi : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (Real.pi : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (Real.pi : ℂ))) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (Real.pi : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (Real.pi : ℂ))) (by ring!))))
      )
  )

theorem h_12 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_25 : Litex.In _value_i1 (Litex.R (M := M))), (by
  let _object_w4 := (let _wd_1_0 := (Litex.exp _value_i1 h_25);
  let _wd_1_1 := (Litex.exp _value_i1 h_25);
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.exp _value_i1 h_25)
    exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.expInRPos _atomic_wd_1_0))) (by
    let _atomic_wd_1_0 := (Litex.exp _value_i1 h_25)
    exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.expInRPos _atomic_wd_1_0)))))
  let _object_w5 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
  let _wd_1_1 := (Litex.exp _value_i1 h_25);
  (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
    let _atomic_wd_1_0 := (Litex.exp _value_i1 h_25)
    exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.expInRPos _atomic_wd_1_0)))))
  exact (by
    let _equal_wd_1_0 := _object_w4
    let _equal_wd_1_1 := _object_w5
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_25
          let _object_w4 := (let _wd_1_0 := (Litex.exp _value_i1 h_25);
          let _wd_1_1 := (Litex.exp _value_i1 h_25);
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.exp _value_i1 h_25)
            exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.expInRPos _atomic_wd_1_0))) (by
            let _atomic_wd_1_0 := (Litex.exp _value_i1 h_25)
            exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.expInRPos _atomic_wd_1_0)))))
          let _object_w5 := (let _wd_1_0 := (Litex.number (M := M) (2 : ℂ));
          let _wd_1_1 := (Litex.exp _value_i1 h_25);
          (Litex.mul _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (2 : ℂ)) (by
            let _atomic_wd_1_0 := (Litex.exp _value_i1 h_25)
            exact (Litex.positiveRealToComplex _atomic_wd_1_0 (Litex.expInRPos _atomic_wd_1_0)))))
          have h_11 : (by
            let _equal_wd_1_0 := _object_w4
            let _equal_wd_1_1 := _object_w5
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w4;
                  let _equal_wd_1_1 := _object_w5;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((let _exp_log := (_equal_wd_1_0).val.left;
                  let _member := Litex.realToComplex _exp_log (Litex.expInR _exp_log);
                  Litex.NativeBridge.asComplex _exp_log _member) + (let _exp_log := (_equal_wd_1_0).val.right;
                  let _member := Litex.realToComplex _exp_log (Litex.expInR _exp_log);
                  Litex.NativeBridge.asComplex _exp_log _member)) ((2 : ℂ) * (let _exp_log := (_equal_wd_1_1).val.right;
                  let _member := Litex.realToComplex _exp_log (Litex.expInR _exp_log);
                  Litex.NativeBridge.asComplex _exp_log _member)) (Litex.NativeBridge.denoteAdd (_equal_wd_1_0).val.left (_equal_wd_1_0).val.right (_equal_wd_1_0).wd.1 (_equal_wd_1_0).wd.2 _ _ (let _exp_log := (_equal_wd_1_0).val.left;
                  let _member := Litex.realToComplex _exp_log (Litex.expInR _exp_log);
                  Litex.NativeBridge.asComplex_spec _exp_log _member) (let _exp_log := (_equal_wd_1_0).val.right;
                  let _member := Litex.realToComplex _exp_log (Litex.expInR _exp_log);
                  Litex.NativeBridge.asComplex_spec _exp_log _member)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) (2 : ℂ)) (_equal_wd_1_1).val.right (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (let _exp_log := (_equal_wd_1_1).val.right;
                  let _member := Litex.realToComplex _exp_log (Litex.expInR _exp_log);
                  Litex.NativeBridge.asComplex_spec _exp_log _member)) (by ring!))))
                )
            )
          exact h_11
        )
      )
  )

noncomputable def _object_i2 := (Litex.formulaFnTarget (M := M) Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => (Litex.realUnaryValue (M := M) Real.exp _raw_i3)) (by
  intro _raw_i3 h_92 _
  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_92)
  have h_92 : Litex.In _value_i3 (Litex.R (M := M)) := h_92
  change (by
    let _atomic_wd_1_0 := (Litex.exp _value_i3 h_92)
    exact Litex.In _atomic_wd_1_0 (Litex.RPos (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.exp _value_i3 h_92)
    exact (Litex.expInRPos _atomic_wd_1_0))))
theorem h_110 : Litex.In (_object_i2 (M := M)) (Litex.fnSet ((_object_i2 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i2 (M := M)))
      )
  )
theorem h_111 : Litex.Same (_object_i2 (M := M)) (_object_i2 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i2 (M := M)))
      )
  )

noncomputable def _object_i4 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (fun (_raw_i5 : M.Value) => (Litex.realUnaryValue (M := M) Real.log _raw_i5)) (by
  intro _raw_i5 h_125 _positive_i5
  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_125)
  have h_125 : Litex.In _value_i5 (Litex.RPos (M := M)) := ((Litex.positiveReal_members (M := M) _raw_i5).mpr ⟨h_125, _positive_i5⟩)
  have h_126 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inRPos_positive _value_i5 h_125)
        )
    )
  have h_127 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.ltToLe (Litex.number (M := M) 0) _value_i5 h_126)
        )
    )
  have h_128 : ¬ Litex.Same _value_i5 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i5 h_126) _litex_zero.symm)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.ln _value_i5 h_125)
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.ln _value_i5 h_125)
    exact (Litex.lnInR _atomic_wd_1_0))))
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

theorem h_156 : ∀ {_Host_i6 : Type v6} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_170 : Litex.In _value_i6 (Litex.R (M := M))), (by
  let _object_w22 := (let _object_w17 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i3 : M.Value) => True) (_object_i2 (M := M)) _value_i6 (h_110 (M := M)) h_170 True.intro);
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _object_w17 (h_153 (M := M)) (Litex.inRPos_real _object_w17 (by
    let _atomic_wd_1_0 := _object_w17
    exact (by
      let _litex_return_call := _object_w17
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))) ((Litex.positiveReal_members (M := M) (Litex.denote _object_w17)).mp (by
    let _atomic_wd_1_0 := _object_w17
    exact (by
      let _litex_return_call := _object_w17
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))).2))
  exact (by
    let _equal_wd_1_0 := _object_w22
    exact Litex.Same _equal_wd_1_0 _value_i6)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i6 _rep_i6 _value_i6 h_170
          let _object_w22 := (let _object_w17 := (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i3 : M.Value) => True) (_object_i2 (M := M)) _value_i6 (h_110 (M := M)) h_170 True.intro);
          (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _object_w17 (h_153 (M := M)) (Litex.inRPos_real _object_w17 (by
            let _atomic_wd_1_0 := _object_w17
            exact (by
              let _litex_return_call := _object_w17
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))) ((Litex.positiveReal_members (M := M) (Litex.denote _object_w17)).mp (by
            let _atomic_wd_1_0 := _object_w17
            exact (by
              let _litex_return_call := _object_w17
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.RPos (M := M)) (Litex.RPos (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.RPos (M := M))) (Litex.callInOutput _litex_return_call)))).2))
          have h_155 : (by
            let _equal_wd_1_0 := _object_w22
            exact Litex.Same _equal_wd_1_0 _value_i6) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w22;
                  (show Litex.Same _equal_wd_1_0 _value_i6 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i6))) = (Litex.denote _value_i6) from by
                    have _litex_residual : ((Litex.realUnaryValue (M := M) Real.log) ((Litex.realUnaryValue (M := M) Real.exp) (Litex.denote _value_i6))) = (Litex.denote _value_i6) := (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.exp _value_i6 h_170);
                    (Litex.ln _wd_1_0 (by
                      let _atomic_wd_1_0 := (Litex.exp _value_i6 h_170)
                      exact (Litex.expInRPos _atomic_wd_1_0))));
                    (show Litex.Same _equal_wd_2_0 _value_i6 from (Litex.lnExp _equal_wd_2_0)))
                    exact ((((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i6))))).trans (congrArg (fun _x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) _x) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i2 (M := M))) (Litex.denote _value_i6)) = ((Litex.realUnaryValue (M := M) Real.exp) (Litex.denote _value_i6)) from by
                    let _litex_original := (_equal_wd_1_0).val.argument
                    let _litex_literal := (let _wd_1_0 := (_object_i2 (M := M));
                    let _wd_1_1 := _value_i6;
                    (Litex.callTarget Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) h_170 True.intro))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_111 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormulaTarget_denote Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i3 : M.Value) => True) (fun (_raw_i3 : M.Value) => (Litex.realUnaryValue (M := M) Real.exp _raw_i3)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.oneTarget_domain Litex.StandardSetValue.real (Litex.denote (Litex.RPos (M := M))) (Litex.isSet (Litex.RPos (M := M))) (fun (_raw_i3 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i3 : M.Value) => (Litex.realUnaryValue (M := M) Real.exp _raw_i3)) (Litex.denote _litex_literal.val.argument) = ((Litex.realUnaryValue (M := M) Real.exp) (Litex.denote _value_i6)) from rfl))
                  )))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) ((Litex.realUnaryValue (M := M) Real.exp) (Litex.denote _value_i6))) = ((Litex.realUnaryValue (M := M) Real.log) ((Litex.realUnaryValue (M := M) Real.exp) (Litex.denote _value_i6))) from by
                    let _litex_original := (let _object_w20 := (Litex.exp _value_i6 h_170);
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (_object_i4 (M := M)) _object_w20 (h_153 (M := M)) (Litex.inRPos_real _object_w20 (by
                      let _atomic_wd_1_0 := _object_w20
                      exact (Litex.expInRPos _atomic_wd_1_0))) ((Litex.positiveReal_members (M := M) (Litex.denote _object_w20)).mp (by
                      let _atomic_wd_1_0 := _object_w20
                      exact (Litex.expInRPos _atomic_wd_1_0))).2))
                    let _litex_literal := (let _wd_1_0 := (_object_i4 (M := M));
                    let _object_w21 := (Litex.exp _value_i6 h_170);
                    (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) _wd_1_0 _object_w21 (Litex.formulaFnInFnSet _wd_1_0) (Litex.inRPos_real _object_w21 (by
                      let _atomic_wd_1_0 := _object_w21
                      exact (Litex.expInRPos _atomic_wd_1_0))) ((Litex.positiveReal_members (M := M) (Litex.denote _object_w21)).mp (by
                      let _atomic_wd_1_0 := _object_w21
                      exact (Litex.expInRPos _atomic_wd_1_0))).2))
                    have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_154 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) (fun (_raw_i5 : M.Value) => (Litex.realUnaryValue (M := M) Real.log _raw_i5)) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i5 : M.Value) => (Litex.positiveRealPredicate (M := M) _raw_i5)) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i5 : M.Value) => (Litex.realUnaryValue (M := M) Real.log _raw_i5)) (Litex.denote _litex_literal.val.argument) = ((Litex.realUnaryValue (M := M) Real.log) ((Litex.realUnaryValue (M := M) Real.exp) (Litex.denote _value_i6))) from rfl))
                  ))).trans _litex_residual)))
                )
            )
          exact h_155
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_exponential_x5f_logarithm_x5f_functions_x2f_statement_x2e_lit
