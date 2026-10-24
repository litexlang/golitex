import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_nonzero_x5f_rational_x5f_reciprocal_x2f_statement_x2e_lit

universe u v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFnOn (Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.QStar (M := M))) (Litex.denote (Litex.QStar (M := M))) (Litex.isSet (Litex.QStar (M := M))) (Litex.isSet (Litex.QStar (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.QStar (M := M))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → M.mem ((fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) _raw_i2) (Litex.denote (Litex.QStar (M := M))) := (by
    intro _raw_i2 h_14 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
    have h_14 : Litex.In _value_i2 (Litex.QStar (M := M)) := h_14
    have h_15 : ¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inQStar_nonzero _value_i2 h_14)
          )
      )
    change (by
      let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i2 (Litex.inQStar_base _value_i2 h_14)) h_15)
      exact Litex.In _atomic_wd_1_0 (Litex.QStar (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i2 (Litex.inQStar_base _value_i2 h_14)) h_15)
      exact (Litex.divInQStar _atomic_wd_1_0 (Litex.inQStar_intro (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInQOfEq (M := M) (1 : ℂ) (1 : ℚ) (by norm_num)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) 0) (1 : ℂ) 0 (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) rfl (by norm_num [Complex.ext_iff]))) h_14)))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.QStar (M := M))) (Litex.denote (Litex.QStar (M := M))) (Litex.isSet (Litex.QStar (M := M))) (Litex.isSet (Litex.QStar (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard))
theorem h_94 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_95 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_w16 := (let _object_w7 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
(let _litex_call_arg_0 := _object_w7;
Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_94 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(by
  let _atomic_wd_1_0 := _object_w7
  exact (Litex.inQStar_intro _atomic_wd_1_0 (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_object_w7).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq (- (2 : ℂ)) (-2 : ℚ) (by norm_num))) (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) 0) (- (2 : ℂ)) 0 (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_object_w7).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) rfl (by norm_num [Complex.ext_iff])))), True.intro⟩)))

noncomputable def _object_w17 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.div _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))

theorem h_96 : (by
  let _equal_wd_1_0 := (_object_w16 (M := M))
  let _equal_wd_1_1 := (_object_w17 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w16 (M := M));
        let _equal_wd_1_1 := (_object_w17 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.negValue (M.number (2 : ℂ)))) = (M.divValue (M.negValue (M.number (1 : ℂ))) (M.number (2 : ℂ))) from by
          have _litex_residual : (M.divValue (M.number (1 : ℂ)) (M.negValue (M.number (2 : ℂ)))) = (M.divValue (M.negValue (M.number (1 : ℂ))) (M.number (2 : ℂ))) := (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
          let _wd_1_1 := (_equal_wd_1_0).val.argument;
          (Litex.div _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : (- (2 : ℂ)) = (-2 : ℂ)))) (Litex.numberInC (M := M) (-2 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (- (2 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))));
          let _equal_wd_2_1 := _equal_wd_1_1;
          (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 _equal_wd_2_1 ((1 : ℂ) / (- (2 : ℂ))) ((- (1 : ℂ)) / (2 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (_equal_wd_2_0).val.right (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2.1 (_equal_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) ((_equal_wd_2_0).val.right).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))) (Litex.NativeBridge.denoteDiv (_equal_wd_2_1).val.left (Litex.number (M := M) (2 : ℂ)) (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2.1 (_equal_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) ((_equal_wd_2_1).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.negValue (M.number (2 : ℂ)))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.negValue (M.number (2 : ℂ)))) = (M.divValue (M.number (1 : ℂ)) (M.negValue (M.number (2 : ℂ)))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
        let _object_w15 := (_equal_wd_1_0).val.argument;
        (let _litex_call_arg_0 := _object_w15;
        Litex.callOnDomain (Litex.QStar (M := M)) (Litex.QStar (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) (by
          let _atomic_wd_1_0 := _object_w15
          exact (Litex.inQStar_intro _atomic_wd_1_0 (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_object_w15).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq (- (2 : ℂ)) (-2 : ℚ) (by norm_num))) (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) 0) (- (2 : ℂ)) 0 (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_object_w15).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) rfl (by norm_num [Complex.ext_iff])))) True.intro))
          have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_95 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
          exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) _litex_input) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (M.negValue (M.number (2 : ℂ)))); exact rfl))
        ))).trans _litex_residual)))
      )
  )

theorem h_296 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_309 : Litex.In _value_i3 (Litex.QStar (M := M))), (by
  let _object_w20 := (let _litex_call_arg_0 := _value_i3;
  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_94 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_309, True.intro⟩))
  let _object_w21 := (let _wd_1_0 := _object_w20;
  let _wd_1_1 := _value_i3;
  (Litex.mul _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _object_w20
    exact (Litex.rationalToComplex _object_w20 (Litex.inQStar_base _object_w20 (Litex.callOnInOutput _object_w20)))) (Litex.rationalToComplex _wd_1_1 (Litex.inQStar_base _wd_1_1 h_309))))
  let _object_w25 := (let _wd_1_0 := _object_w20;
  (let _litex_call_arg_0 := _wd_1_0;
  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_94 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(by
    let _atomic_wd_1_0 := _object_w20
    exact (by
      let _litex_return_call := _object_w20
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.QStar (M := M)) (Litex.QStar (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.QStar (M := M))) (Litex.callOnInOutput _litex_return_call))), True.intro⟩)))
  exact (((by
    let _atomic_wd_1_0 := _object_w20
    exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))) ∧ ((((by
    let _equal_wd_1_0 := _object_w21
    exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ)))) ∧ ((by
    let _equal_wd_1_0 := _object_w25
    exact Litex.Same _equal_wd_1_0 _value_i3)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i3 _rep_i3 _value_i3 h_309
          have h_310 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inQStar_nonzero _value_i3 h_309)
                )
            )
          let _object_w20 := (let _litex_call_arg_0 := _value_i3;
          Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_94 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨h_309, True.intro⟩))
          have h_293 : (by
            let _atomic_wd_1_0 := _object_w20
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := _object_w20
                    exact (Litex.notSameOfMembership _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (Litex.QStar (M := M)) (by
                      let _atomic_wd_2_0 := _atomic_wd_1_0
                      exact (by
                        let _litex_return_call := _atomic_wd_2_0
                        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.QStar (M := M)) (Litex.QStar (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.QStar (M := M))) (Litex.callOnInOutput _litex_return_call))) (Litex.notInOfSame (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (((0 : ℚ) : ℚ) : ℂ)) (Litex.QStar (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (((0 : ℚ) : ℚ) : ℂ)))) (fun _member => (Litex.inQStar_nonzero (Litex.number (M := M) (((0 : ℚ) : ℚ) : ℂ)) _member) (congrArg M.number (by norm_num : (((0 : ℚ) : ℚ) : ℂ) = (0 : ℂ)))))))
                )
            )
          let _object_w21 := (let _wd_1_0 := _object_w20;
          let _wd_1_1 := _value_i3;
          (Litex.mul _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w20
            exact (Litex.rationalToComplex _object_w20 (Litex.inQStar_base _object_w20 (Litex.callOnInOutput _object_w20)))) (Litex.rationalToComplex _wd_1_1 (Litex.inQStar_base _wd_1_1 h_309))))
          have h_294 : (by
            let _equal_wd_1_0 := _object_w21
            exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (1 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (((congrArg₂ M.mulValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3)) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i3)) from by
                    let _litex_original := _object_w20
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                  let _wd_1_1 := _value_i3;
                  (let _litex_call_arg_0 := _wd_1_1;
                  Litex.callOnDomain (Litex.QStar (M := M)) (Litex.QStar (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) h_309 True.intro))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_95 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) _litex_input) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.denote _value_i3)); exact rfl))
                  ) (Eq.refl (Litex.denote _value_i3)))).trans (((let _equal_wd_2_0 := (let _wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i3 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i3 (Litex.inQStar_base _value_i3 h_309)) h_310);
                  let _wd_1_1 := _value_i3;
                  (Litex.mul _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := _wd_1_0
                    exact (Litex.divInC (Litex.number (M := M) (1 : ℂ)) _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.rationalToComplex _wd_1_1 (Litex.inQStar_base _wd_1_1 h_309)) (_atomic_wd_1_0).wd.2.2)) (Litex.rationalToComplex _wd_1_1 (Litex.inQStar_base _wd_1_1 h_309))));
                  (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (1 : ℂ)) from (by
                    let _quotient := (_equal_wd_2_0).val.left
                    let _product := _equal_wd_2_0
                    have _child : (by
                      let _equal_wd_3_0 := (_equal_wd_2_0).val.left
                      let _equal_wd_3_1 := _equal_wd_3_0
                      exact Litex.Same _equal_wd_3_1 _equal_wd_3_1) := (show @Eq M.Value _ _ from Eq.refl _)
                    have _conversion := Litex.sameDivIffSameMul _quotient.val.left _quotient.val.right _product.val.left _quotient.wd.1 _quotient.wd.2.1 _product.wd.1 _quotient.wd.2.2
                    exact ((_conversion.mp _child).symm))))).trans ((Eq.refl (M.number (1 : ℂ)))).symm))
                )
            )
          let _object_w25 := (let _wd_1_0 := _object_w20;
          (let _litex_call_arg_0 := _wd_1_0;
          Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_94 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(by
            let _atomic_wd_1_0 := _object_w20
            exact (by
              let _litex_return_call := _object_w20
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.QStar (M := M)) (Litex.QStar (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.QStar (M := M))) (Litex.callOnInOutput _litex_return_call))), True.intro⟩)))
          have h_295 : (by
            let _equal_wd_1_0 := _object_w25
            exact Litex.Same _equal_wd_1_0 _value_i3) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w25;
                  (show Litex.Same _equal_wd_1_0 _value_i3 from (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3))) = (M.divValue (M.number (1 : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3))) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                  let _wd_1_1 := _object_w20;
                  (let _litex_call_arg_0 := _wd_1_1;
                  Litex.callOnDomain (Litex.QStar (M := M)) (Litex.QStar (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) (by
                    let _atomic_wd_1_0 := _object_w20
                    exact (by
                      let _litex_return_call := _object_w20
                      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.QStar (M := M)) (Litex.QStar (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.QStar (M := M))) (Litex.callOnInOutput _litex_return_call))) True.intro))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_95 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) _litex_input) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.denote _value_i3))); exact rfl))
                  )).trans (((let _equal_wd_2_0 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
                  let _wd_1_1 := _object_w20;
                  (Litex.div _wd_1_0 _wd_1_1 (Litex.numberInC (M := M) (1 : ℂ)) (by
                    let _atomic_wd_1_0 := _object_w20
                    exact (Litex.rationalToComplex _object_w20 (Litex.inQStar_base _object_w20 (Litex.callOnInOutput _object_w20)))) (by
                    let _atomic_wd_1_0 := _object_w20
                    exact h_293)));
                  (show Litex.Same _equal_wd_2_0 _value_i3 from (by
                    let _quotient := _equal_wd_2_0
                    let _product := _object_w21
                    have _child : (by
                      let _equal_wd_3_1 := _object_w21
                      exact Litex.Same (Litex.number (M := M) (1 : ℂ)) _equal_wd_3_1) := (h_294).symm
                    have _conversion := Litex.sameDivIffSameMul _quotient.val.left _quotient.val.right _product.val.right _quotient.wd.1 _quotient.wd.2.1 _product.wd.2 _quotient.wd.2.2
                    exact (_conversion.mpr (_child.trans (Litex.sameMulComm _product.val.left _product.val.right _product.wd.1 _product.wd.2))))))).trans ((Eq.refl (Litex.denote _value_i3))).symm))))
                )
            )
          exact (And.intro h_293 (And.intro h_294 h_295))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_nonzero_x5f_rational_x5f_reciprocal_x2f_statement_x2e_lit
