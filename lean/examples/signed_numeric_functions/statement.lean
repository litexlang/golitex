import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_signed_x5f_numeric_x5f_functions_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFnOn (let _litex_output := (Litex.Q (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.QStar (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.QStar (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i2 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.QStar (M := M))) → ((fun (_raw_i2 : M.Value) => True) _raw_i2) → M.mem ((fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) _raw_i2) (Litex.denote (Litex.Q (M := M))) := (by
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
      exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.numberInC (M := M) (1 : ℂ)) (Litex.rationalToComplex _value_i2 (Litex.inQStar_base _value_i2 h_14)) h_15)
      exact (Litex.divInQ (Litex.number (M := M) (1 : ℂ)) _value_i2 (Litex.NativeBridge.numberInQOfEq (M := M) (1 : ℂ) (1 : ℚ) (by norm_num)) (Litex.inQStar_base _value_i2 h_14) (_atomic_wd_1_0).wd.2.2)))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.QStar (M := M))) (Litex.denote (Litex.Q (M := M))) (Litex.isSet (Litex.QStar (M := M))) (Litex.isSet (Litex.Q (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard))
theorem h_83 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_84 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_w16 := (let _object_w7 := (Litex.neg (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)));
(let _litex_call_arg_0 := _object_w7;
Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) _litex_call_arg_0 (h_83 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(by
  let _atomic_wd_1_0 := _object_w7
  exact (Litex.inQStar_intro _atomic_wd_1_0 (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_object_w7).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq (- (2 : ℂ)) (-2 : ℚ) (by norm_num))) (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) 0) (- (2 : ℂ)) 0 (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_object_w7).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) rfl (by norm_num [Complex.ext_iff])))), True.intro⟩)))

noncomputable def _object_w17 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.div _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-1 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)))).trans (congrArg M.number (by norm_num : (- (1 : ℂ)) = (-1 : ℂ)))) (Litex.numberInC (M := M) (-1 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))

theorem h_85 : (by
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
        Litex.callOnDomain (Litex.QStar (M := M)) (Litex.Q (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) (by
          let _atomic_wd_1_0 := _object_w15
          exact (Litex.inQStar_intro _atomic_wd_1_0 (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_object_w15).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq (- (2 : ℂ)) (-2 : ℚ) (by norm_num))) (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) 0) (- (2 : ℂ)) 0 (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_object_w15).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) rfl (by norm_num [Complex.ext_iff])))) True.intro))
          have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_84 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
          exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) => (M.divValue (M.number (1 : ℂ)) _raw_i2)) _litex_input) (Litex.denote _litex_literal.val.argument) = (M.divValue (M.number (1 : ℂ)) (M.negValue (M.number (2 : ℂ)))); exact rfl))
        ))).trans _litex_residual)))
      )
  )

noncomputable def _object_i3 := (Litex.formulaFnOn (let _litex_output := (Litex.ZNeg (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.ZNeg (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.ZNeg (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => _raw_i4) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i4 : M.Value), M.mem _raw_i4 (Litex.denote (Litex.ZNeg (M := M))) → ((fun (_raw_i4 : M.Value) => True) _raw_i4) → M.mem ((fun (_raw_i4 : M.Value) => _raw_i4) _raw_i4) (Litex.denote (Litex.ZNeg (M := M))) := (by
    intro _raw_i4 h_295 _
    let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_295)
    have h_295 : Litex.In _value_i4 (Litex.ZNeg (M := M)) := h_295
    have h_296 : Litex.Lt _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inZNeg_negative _value_i4 h_295)
          )
      )
    have h_297 : Litex.Le _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe _value_i4 (Litex.number (M := M) 0) h_296)
          )
      )
    have h_298 : ¬ Litex.Same _value_i4 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltNotSame _value_i4 (Litex.number (M := M) 0) h_296)
          )
      )
    change Litex.In _value_i4 (Litex.ZNeg (M := M))
    exact h_295)
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.ZNeg (M := M))) (Litex.denote (Litex.ZNeg (M := M))) (Litex.isSet (Litex.ZNeg (M := M))) (Litex.isSet (Litex.ZNeg (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard))
theorem h_308 : Litex.In (_object_i3 (M := M)) (Litex.fnSet ((_object_i3 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i3 (M := M)))
      )
  )
theorem h_309 : Litex.Same (_object_i3 (M := M)) (_object_i3 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i3 (M := M)))
      )
  )

noncomputable def _object_w33 := (let _object_w24 := ((_object_w16 (M := M))).val.argument;
(let _litex_call_arg_0 := _object_w24;
Litex.callOn ((_object_i3 (M := M))).val.signature (_object_i3 (M := M)) _litex_call_arg_0 (h_308 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(by
  let _atomic_wd_1_0 := _object_w24
  exact (Litex.inZNeg_intro _atomic_wd_1_0 (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_object_w24).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num))) (Litex.NativeBridge.ltOfDenoteReal _atomic_wd_1_0 (Litex.number (M := M) 0) (-2 : ℝ) 0 (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_object_w24).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : (- (2 : ℂ)) = ((-2 : ℝ) : ℂ)))) rfl (by norm_num)))), True.intro⟩)))

noncomputable def _object_w34 := ((_object_w16 (M := M))).val.argument

theorem h_310 : (by
  let _equal_wd_1_0 := (_object_w33 (M := M))
  let _equal_wd_1_1 := (_object_w34 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w33 (M := M));
        let _equal_wd_1_1 := (_object_w34 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.negValue (M.number (2 : ℂ)))) = (M.negValue (M.number (2 : ℂ))) from by
          have _litex_residual : (M.negValue (M.number (2 : ℂ))) = (M.negValue (M.number (2 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.negValue (M.number (2 : ℂ)))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (M.negValue (M.number (2 : ℂ)))) = (M.negValue (M.number (2 : ℂ))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i3 (M := M));
        let _object_w32 := _equal_wd_1_1;
        (let _litex_call_arg_0 := _object_w32;
        Litex.callOnDomain (Litex.ZNeg (M := M)) (Litex.ZNeg (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) (by
          let _atomic_wd_1_0 := _object_w32
          exact (Litex.inZNeg_intro _atomic_wd_1_0 (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (2 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_object_w32).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (2 : ℂ)) (-2 : ℤ) (by norm_num))) (Litex.NativeBridge.ltOfDenoteReal _atomic_wd_1_0 (Litex.number (M := M) 0) (-2 : ℝ) 0 (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) (_object_w32).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : (- (2 : ℂ)) = ((-2 : ℝ) : ℂ)))) rfl (by norm_num)))) True.intro))
          have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_309 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
          exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i4 : M.Value) => _raw_i4) _litex_input) (Litex.denote _litex_literal.val.argument) = (M.negValue (M.number (2 : ℂ))); exact rfl))
        ))).trans _litex_residual)))
      )
  )

noncomputable def _object_w35 := (let _wd_1_0 := (_object_w33 (M := M));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.add _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := (_object_w33 (M := M))
  exact (Litex.integerToComplex (_object_w33 (M := M)) (Litex.inZNeg_base (_object_w33 (M := M)) (Litex.callOnInOutput (_object_w33 (M := M)))))) (Litex.numberInC (M := M) (2 : ℂ))))

theorem h_554 : (by
  let _equal_wd_1_0 := (_object_w35 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (((congrArg₂ M.addValue (h_310 (M := M)) (Litex.sameRefl (Litex.number (M := M) (2 : ℂ))))).trans (((let _equal_wd_2_0 := (let _wd_1_0 := (_object_w34 (M := M));
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.add _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (_object_w34 (M := M))
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-2 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) ((_object_w34 (M := M))).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : (- (2 : ℂ)) = (-2 : ℂ)))) (Litex.numberInC (M := M) (-2 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ))));
        (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (0 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (0 : ℂ)) ((- (2 : ℂ)) + (2 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteAdd (_equal_wd_2_0).val.left (Litex.number (M := M) (2 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (2 : ℂ)) ((_object_w34 (M := M))).wd _ (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))).trans ((Litex.sameRefl (Litex.number (M := M) (0 : ℂ)))).symm))
      )
  )

noncomputable def _object_i5 := (Litex.formulaFnOn (let _litex_output := (Litex.CStar (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.CStar (M := M))) (Litex.denote _litex_output) (Litex.isSet (Litex.CStar (M := M))) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => _raw_i6) _litex_input) (by
  have _litex_checked_return : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote (Litex.CStar (M := M))) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → M.mem ((fun (_raw_i6 : M.Value) => _raw_i6) _raw_i6) (Litex.denote (Litex.CStar (M := M))) := (by
    intro _raw_i6 h_781 _
    let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_781)
    have h_781 : Litex.In _value_i6 (Litex.CStar (M := M)) := h_781
    have h_782 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inCStar_nonzero _value_i6 h_781)
          )
      )
    change Litex.In _value_i6 (Litex.CStar (M := M))
    exact h_781)
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.denote (Litex.CStar (M := M))) (Litex.denote (Litex.CStar (M := M))) (Litex.isSet (Litex.CStar (M := M))) (Litex.isSet (Litex.CStar (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _litex_input).mp _litex_domain
  exact _litex_checked_return _litex_input _litex_members _litex_guard))
theorem h_790 : Litex.In (_object_i5 (M := M)) (Litex.fnSet ((_object_i5 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i5 (M := M)))
      )
  )
theorem h_791 : Litex.Same (_object_i5 (M := M)) (_object_i5 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i5 (M := M)))
      )
  )

noncomputable def _object_w41 := (let _litex_call_arg_0 := (Litex.number (M := M) Complex.I);
Litex.callOn ((_object_i5 (M := M))).val.signature (_object_i5 (M := M)) _litex_call_arg_0 (h_790 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.inCStar_intro (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) Complex.I) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) Complex.I) (Litex.number (M := M) 0) Complex.I 0 (Litex.NativeBridge.denoteNumber (M := M) Complex.I) rfl (by norm_num [Complex.ext_iff]))), True.intro⟩))

theorem h_792 : (by
  let _equal_wd_1_0 := (_object_w41 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) Complex.I)) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w41 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) Complex.I) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote (Litex.number (M := M) Complex.I))) = (Litex.denote (Litex.number (M := M) Complex.I)) from by
          have _litex_residual : (Litex.denote (Litex.number (M := M) Complex.I)) = (Litex.denote (Litex.number (M := M) Complex.I)) := (show @Eq M.Value _ _ from Eq.refl _)
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote (Litex.number (M := M) Complex.I))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote (Litex.number (M := M) Complex.I))) = (Litex.denote (Litex.number (M := M) Complex.I)) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i5 (M := M));
        let _wd_1_1 := (Litex.number (M := M) Complex.I);
        (let _litex_call_arg_0 := _wd_1_1;
        Litex.callOnDomain (Litex.CStar (M := M)) (Litex.CStar (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) (Litex.inCStar_intro _wd_1_1 (Litex.numberInC (M := M) Complex.I) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) 0) Complex.I 0 (Litex.NativeBridge.denoteNumber (M := M) Complex.I) rfl (by norm_num [Complex.ext_iff]))) True.intro))
          have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_791 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
          exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => _raw_i6) _litex_input) (Litex.denote _litex_literal.val.argument) = (Litex.denote (Litex.number (M := M) Complex.I)); exact rfl))
        ))).trans _litex_residual)))
      )
  )

noncomputable def _object_w43 := (let _wd_1_0 := (_object_w41 (M := M));
let _wd_1_1 := (Litex.number (M := M) Complex.I);
(Litex.mul _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := (_object_w41 (M := M))
  exact (Litex.inCStar_base (_object_w41 (M := M)) (Litex.callOnInOutput (_object_w41 (M := M))))) (Litex.numberInC (M := M) Complex.I)))

noncomputable def _object_w44 := ((_object_w17 (M := M))).val.left

theorem h_840 : (by
  let _equal_wd_1_0 := (_object_w43 (M := M))
  let _equal_wd_1_1 := (_object_w44 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w43 (M := M));
        let _equal_wd_1_1 := (_object_w44 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((congrArg₂ M.mulValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i5 (M := M))) (Litex.denote (Litex.number (M := M) Complex.I))) = (Litex.denote (Litex.number (M := M) Complex.I)) from by
          let _litex_original := (_object_w41 (M := M))
          let _litex_literal := (let _wd_1_0 := (_object_i5 (M := M));
        let _wd_1_1 := (Litex.number (M := M) Complex.I);
        (let _litex_call_arg_0 := _wd_1_1;
        Litex.callOnDomain (Litex.CStar (M := M)) (Litex.CStar (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _wd_1_0 _litex_call_arg_0 (Litex.formulaFnInFnSet _wd_1_0) (Litex.inCStar_intro _wd_1_1 (Litex.numberInC (M := M) Complex.I) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) 0) Complex.I 0 (Litex.NativeBridge.denoteNumber (M := M) Complex.I) rfl (by norm_num [Complex.ext_iff]))) True.intro))
          have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_791 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
          exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => _raw_i6) _litex_input) (Litex.denote _litex_literal.val.argument) = (Litex.denote (Litex.number (M := M) Complex.I)); exact rfl))
        ) (Eq.refl (Litex.denote (Litex.number (M := M) Complex.I))))).trans (((let _equal_wd_2_0 := (Litex.mul (Litex.number (M := M) Complex.I) (Litex.number (M := M) Complex.I) (Litex.numberInC (M := M) Complex.I) (Litex.numberInC (M := M) Complex.I));
        let _equal_wd_2_1 := _equal_wd_1_1;
        (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 _equal_wd_2_1 (Complex.I * Complex.I) (- (1 : ℂ)) (Litex.NativeBridge.denoteMul (Litex.number (M := M) Complex.I) (Litex.number (M := M) Complex.I) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) Complex.I) (Litex.NativeBridge.denoteNumber (M := M) Complex.I)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (1 : ℂ)) (_equal_wd_2_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (by norm_num [Complex.ext_iff]))))).trans ((Eq.refl (M.negValue (M.number (1 : ℂ))))).symm))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_signed_x5f_numeric_x5f_functions_x2f_statement_x2e_lit
