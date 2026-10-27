import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_real_x5f_functions_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (fun (_raw_i2 : M.Value) => (Litex.roundingValue (M := M) false _raw_i2)) (by
  intro _raw_i2 h_14 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_14)
  have h_14 : Litex.In _value_i2 (Litex.R (M := M)) := h_14
  change (by
    let _atomic_wd_1_0 := (Litex.floor _value_i2 h_14)
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.floor _value_i2 h_14)
    exact (Litex.roundingInZ _atomic_wd_1_0))))
theorem h_32 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_33 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem h_66 : (by
  let _equal_wd_1_0 := (let _object_w7 := (let _wd_2_0 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)));
  let _wd_2_1 := (Litex.number (M := M) (3 : ℂ));
  (Litex.div _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-7 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)))).trans (congrArg M.number (by norm_num : (- (7 : ℂ)) = (-7 : ℂ)))) (Litex.numberInC (M := M) (-7 : ℂ)))) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w7 (h_32 (M := M)) (by
    let _atomic_wd_1_0 := _object_w7
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((- (7 : ℂ)) / (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (_object_w7).val.left (Litex.number (M := M) (3 : ℂ)) (_object_w7).wd.1 (_object_w7).wd.2.1 (_object_w7).wd.2.2 _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) ((_object_w7).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((- (7 : ℂ)) / (3 : ℂ)) ((-7 : ℝ) / (3 : ℝ)) (by norm_num)))) True.intro))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (-3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _object_w7 := (let _wd_2_0 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)));
        let _wd_2_1 := (Litex.number (M := M) (3 : ℂ));
        (Litex.div _wd_2_0 _wd_2_1 (by
          let _atomic_wd_1_0 := _wd_2_0
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-7 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)))).trans (congrArg M.number (by norm_num : (- (7 : ℂ)) = (-7 : ℂ)))) (Litex.numberInC (M := M) (-7 : ℂ)))) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w7 (h_32 (M := M)) (by
          let _atomic_wd_1_0 := _object_w7
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((- (7 : ℂ)) / (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (_object_w7).val.left (Litex.number (M := M) (3 : ℂ)) (_object_w7).wd.1 (_object_w7).wd.2.1 (_object_w7).wd.2.2 _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) ((_object_w7).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((- (7 : ℂ)) / (3 : ℂ)) ((-7 : ℝ) / (3 : ℝ)) (by norm_num)))) True.intro));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (-3 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (-3 : ℂ)) from ((show Litex.denote _equal_wd_1_0 = M.number (-3 : ℂ) from by simpa only [M.neg_numbers] using ((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.divValue (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ)))))).trans (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (M.divValue (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ)))) = ((Litex.roundingValue (M := M) false) (M.divValue (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ)))) from by
          let _litex_original := (let _object_w6 := (let _wd_2_0 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)));
        let _wd_2_1 := (Litex.number (M := M) (3 : ℂ));
        (Litex.div _wd_2_0 _wd_2_1 (by
          let _atomic_wd_1_0 := _wd_2_0
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-7 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)))).trans (congrArg M.number (by norm_num : (- (7 : ℂ)) = (-7 : ℂ)))) (Litex.numberInC (M := M) (-7 : ℂ)))) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
        (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w6 (h_32 (M := M)) (by
          let _atomic_wd_1_0 := _object_w6
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((- (7 : ℂ)) / (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (_object_w6).val.left (Litex.number (M := M) (3 : ℂ)) (_object_w6).wd.1 (_object_w6).wd.2.1 (_object_w6).wd.2.2 _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) ((_object_w6).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((- (7 : ℂ)) / (3 : ℂ)) ((-7 : ℝ) / (3 : ℝ)) (by norm_num)))) True.intro))
          let _litex_formula := (_object_i1 (M := M))
          have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := (h_33 (M := M))
          have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.denote _litex_original.val.argument)) _litex_head_eq
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.denote _litex_original.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) _).mpr _litex_original.wd.2)
          simpa only [M.neg_numbers] using _litex_call_eq.trans (_litex_beta.trans (show _litex_formula.val.bodyValue (Litex.denote _litex_original.val.argument) = ((Litex.roundingValue (M := M) false) (M.divValue (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ)))) from by simp only [M.neg_numbers]))
        )).trans (((Eq.refl ((Litex.roundingValue (M := M) false) (M.divValue (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ)))))).trans (show ((Litex.roundingValue (M := M) false) (M.divValue (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ)))) = M.number (-3 : ℂ) from (congrArg (Litex.roundingValue (M := M) false) (show (M.divValue (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ))) = M.number ((-7 : ℂ) / (3 : ℂ)) from ((congrArg₂ M.divValue (show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num))))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((M.div_numbers (-7 : ℂ) (3 : ℂ) (by norm_num)).trans (congrArg M.number (by norm_num)))))).trans (by
          have _numeric := Litex.roundingValue_number false (M := M) ((-7 : ℝ) / (3 : ℝ))
          norm_num [Real.sign] at _numeric
          simpa only [neg_div] using _numeric)))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))).symm)))
      )
  )

theorem h_83 : (by
  let _equal_wd_1_0 := (let _object_w7 := (let _wd_2_0 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)));
  let _wd_2_1 := (Litex.number (M := M) (3 : ℂ));
  (Litex.div _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-7 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)))).trans (congrArg M.number (by norm_num : (- (7 : ℂ)) = (-7 : ℂ)))) (Litex.numberInC (M := M) (-7 : ℂ)))) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
  (Litex.call Litex.StandardSetValue.real Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) => True) (_object_i1 (M := M)) _object_w7 (h_32 (M := M)) (by
    let _atomic_wd_1_0 := _object_w7
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((- (7 : ℂ)) / (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (_object_w7).val.left (Litex.number (M := M) (3 : ℂ)) (_object_w7).wd.1 (_object_w7).wd.2.1 (_object_w7).wd.2.2 _ _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) ((_object_w7).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((- (7 : ℂ)) / (3 : ℂ)) ((-7 : ℝ) / (3 : ℝ)) (by norm_num)))) True.intro))
  let _equal_wd_1_1 := (Litex.number (M := M) (-3 : ℂ))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (h_66 (M := M))
      )
  )

noncomputable def _object_i3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (Litex.minMaxValue (M := M) true (Litex.absValue (M := M) _raw_i4) (Litex.minMaxValue (M := M) false _raw_i5 (M.number (2 : ℂ))))) (by
  intro _raw_i4 _raw_i5 h_111 h_112 _
  let _value_i4 := Litex.semanticObject (M := M) _raw_i4 (M.member_isSet h_111)
  have h_111 : Litex.In _value_i4 (Litex.R (M := M)) := h_111
  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_112)
  have h_112 : Litex.In _value_i5 (Litex.R (M := M)) := h_112
  change (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.abs _value_i4 h_111);
    let _wd_1_1 := (Litex.min _value_i5 (Litex.number (M := M) (2 : ℂ)) h_112 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)));
    (Litex.max _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (by
        let _litex_abs := _atomic_wd_2_0
        exact Litex.absInR _litex_abs.val.arg _litex_abs.wd
      )) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (by
        let _extremum := _atomic_wd_2_0
        exact Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2
      ))))
    exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
  exact (by
    let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.abs _value_i4 h_111);
    let _wd_1_1 := (Litex.min _value_i5 (Litex.number (M := M) (2 : ℂ)) h_112 (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num)));
    (Litex.max _wd_1_0 _wd_1_1 (by
      let _atomic_wd_2_0 := _wd_1_0
      exact (by
        let _litex_abs := _atomic_wd_2_0
        exact Litex.absInR _litex_abs.val.arg _litex_abs.wd
      )) (by
      let _atomic_wd_2_0 := _wd_1_1
      exact (by
        let _extremum := _atomic_wd_2_0
        exact Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2
      ))))
    exact (by
      let _extremum := _atomic_wd_1_0
      exact Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2
    ))))
theorem h_261 : Litex.In (_object_i3 (M := M)) (Litex.fnSet ((_object_i3 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i3 (M := M)))
      )
  )
theorem h_262 : Litex.Same (_object_i3 (M := M)) (_object_i3 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i3 (M := M)))
      )
  )

theorem h_327 : (by
  let _equal_wd_1_0 := (let _object_w18 := (let _wd_2_0 := (Litex.number (M := M) (-3 : ℂ));
  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.div _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
  let _object_w19 := (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (_object_i3 (M := M)) _object_w18 _object_w19 (h_261 (M := M)) (by
    let _atomic_wd_1_0 := _object_w18
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((-3 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (_object_w18).val.left (Litex.number (M := M) (2 : ℂ)) (_object_w18).wd.1 (_object_w18).wd.2.1 (_object_w18).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-3 : ℂ) / (2 : ℂ)) ((-3 : ℝ) / (2 : ℝ)) (by norm_num)))) (by
    let _atomic_wd_1_0 := _object_w19
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((5 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_w19).wd.1 (_object_w19).wd.2.1 (_object_w19).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((5 : ℂ) / (2 : ℂ)) ((5 : ℝ) / (2 : ℝ)) (by norm_num)))) True.intro))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _object_w18 := (let _wd_2_0 := (Litex.number (M := M) (-3 : ℂ));
        let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.div _wd_2_0 _wd_2_1 (by
          let _atomic_wd_1_0 := _wd_2_0
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
        let _object_w19 := (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (_object_i3 (M := M)) _object_w18 _object_w19 (h_261 (M := M)) (by
          let _atomic_wd_1_0 := _object_w18
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((-3 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (_object_w18).val.left (Litex.number (M := M) (2 : ℂ)) (_object_w18).wd.1 (_object_w18).wd.2.1 (_object_w18).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-3 : ℂ) / (2 : ℂ)) ((-3 : ℝ) / (2 : ℝ)) (by norm_num)))) (by
          let _atomic_wd_1_0 := _object_w19
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((5 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_w19).wd.1 (_object_w19).wd.2.1 (_object_w19).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((5 : ℂ) / (2 : ℂ)) ((5 : ℝ) / (2 : ℝ)) (by norm_num)))) True.intro));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from ((show Litex.denote _equal_wd_1_0 = M.number (2 : ℂ) from by simpa only [M.neg_numbers] using ((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.divValue (M.negValue (M.number (3 : ℂ))) (M.number (2 : ℂ))), (M.divValue (M.number (5 : ℂ)) (M.number (2 : ℂ)))])))).trans (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i3 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.divValue (M.negValue (M.number (3 : ℂ))) (M.number (2 : ℂ))), (M.divValue (M.number (5 : ℂ)) (M.number (2 : ℂ)))])) = ((Litex.minMaxValue (M := M) true) (Litex.absValue (M := M) (M.divValue (M.negValue (M.number (3 : ℂ))) (M.number (2 : ℂ)))) ((Litex.minMaxValue (M := M) false) (M.divValue (M.number (5 : ℂ)) (M.number (2 : ℂ))) (M.number (2 : ℂ)))) from by
          let _litex_original := (let _object_w16 := (let _wd_2_0 := (Litex.number (M := M) (-3 : ℂ));
        let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.div _wd_2_0 _wd_2_1 (by
          let _atomic_wd_1_0 := _wd_2_0
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
        let _object_w17 := (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (_object_i3 (M := M)) _object_w16 _object_w17 (h_261 (M := M)) (by
          let _atomic_wd_1_0 := _object_w16
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((-3 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (_object_w16).val.left (Litex.number (M := M) (2 : ℂ)) (_object_w16).wd.1 (_object_w16).wd.2.1 (_object_w16).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-3 : ℂ) / (2 : ℂ)) ((-3 : ℝ) / (2 : ℝ)) (by norm_num)))) (by
          let _atomic_wd_1_0 := _object_w17
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((5 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_w17).wd.1 (_object_w17).wd.2.1 (_object_w17).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((5 : ℂ) / (2 : ℂ)) ((5 : ℝ) / (2 : ℝ)) (by norm_num)))) True.intro))
          let _litex_formula := (_object_i3 (M := M))
          have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := (h_262 (M := M))
          have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.FiniteFunction.pack2 (M := M) (Litex.denote _litex_original.val.first) (Litex.denote _litex_original.val.second))) _litex_head_eq
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.FiniteFunction.pack2 (M := M) (Litex.denote _litex_original.val.first) (Litex.denote _litex_original.val.second)) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) _ _).mpr _litex_original.wd.2)
          simpa only [M.neg_numbers] using _litex_call_eq.trans (_litex_beta.trans (show _litex_formula.val.bodyValue (Litex.FiniteFunction.pack2 (M := M) (Litex.denote _litex_original.val.first) (Litex.denote _litex_original.val.second)) = ((Litex.minMaxValue (M := M) true) (Litex.absValue (M := M) (M.divValue (M.negValue (M.number (3 : ℂ))) (M.number (2 : ℂ)))) ((Litex.minMaxValue (M := M) false) (M.divValue (M.number (5 : ℂ)) (M.number (2 : ℂ))) (M.number (2 : ℂ)))) from by simpa only [M.neg_numbers] using congrArg (fun (_pair : M.Value × M.Value) => (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => (Litex.minMaxValue (M := M) true (Litex.absValue (M := M) _raw_i4) (Litex.minMaxValue (M := M) false _raw_i5 (M.number (2 : ℂ))))) _pair.1 _pair.2) (Litex.FiniteFunction.unpack_pack2 (M := M) (Litex.denote _litex_original.val.first) (Litex.denote _litex_original.val.second))))
        )).trans (((Eq.refl ((Litex.minMaxValue (M := M) true) (Litex.absValue (M := M) (M.divValue (M.negValue (M.number (3 : ℂ))) (M.number (2 : ℂ)))) ((Litex.minMaxValue (M := M) false) (M.divValue (M.number (5 : ℂ)) (M.number (2 : ℂ))) (M.number (2 : ℂ)))))).trans (show ((Litex.minMaxValue (M := M) true) (Litex.absValue (M := M) (M.divValue (M.negValue (M.number (3 : ℂ))) (M.number (2 : ℂ)))) ((Litex.minMaxValue (M := M) false) (M.divValue (M.number (5 : ℂ)) (M.number (2 : ℂ))) (M.number (2 : ℂ)))) = M.number (2 : ℂ) from (congrArg₂ (Litex.minMaxValue (M := M) true) (show (Litex.absValue (M := M) (M.divValue (M.negValue (M.number (3 : ℂ))) (M.number (2 : ℂ)))) = M.number ((3 : ℂ) / (2 : ℂ)) from (congrArg (Litex.absValue (M := M)) (show (M.divValue (M.negValue (M.number (3 : ℂ))) (M.number (2 : ℂ))) = M.number ((-3 : ℂ) / (2 : ℂ)) from ((congrArg₂ M.divValue (show (M.negValue (M.number (3 : ℂ))) = M.number (-3 : ℂ) from ((congrArg M.negValue (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((M.neg_numbers (3 : ℂ)).trans (congrArg M.number (by norm_num))))) (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num)))).trans ((M.div_numbers (-3 : ℂ) (2 : ℂ) (by norm_num)).trans (congrArg M.number (by norm_num)))))).trans (by
          have _numeric := Litex.absValue_number (M := M) ((-3 : ℝ) / (2 : ℝ))
          norm_num [Real.sign] at _numeric
          simpa only [neg_div] using _numeric)) (show ((Litex.minMaxValue (M := M) false) (M.divValue (M.number (5 : ℂ)) (M.number (2 : ℂ))) (M.number (2 : ℂ))) = M.number (2 : ℂ) from (congrArg₂ (Litex.minMaxValue (M := M) false) (show (M.divValue (M.number (5 : ℂ)) (M.number (2 : ℂ))) = M.number ((5 : ℂ) / (2 : ℂ)) from ((congrArg₂ M.divValue (show (M.number (5 : ℂ)) = M.number (5 : ℂ) from (congrArg M.number (show (5 : ℂ) = (5 : ℂ) from by norm_num))) (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num)))).trans ((M.div_numbers (5 : ℂ) (2 : ℂ) (by norm_num)).trans (congrArg M.number (by norm_num))))) (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num)))).trans (by
          have _numeric := Litex.minMaxValue_number false (M := M) ((5 : ℝ) / (2 : ℝ)) (2 : ℝ)
          norm_num [Real.sign] at _numeric
          simpa only [neg_div] using _numeric))).trans (by
          have _numeric := Litex.minMaxValue_number true (M := M) ((3 : ℝ) / (2 : ℝ)) (2 : ℝ)
          norm_num [Real.sign] at _numeric
          simpa only [neg_div] using _numeric)))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))).symm)))
      )
  )

theorem h_360 : (by
  let _equal_wd_1_0 := (let _object_w18 := (let _wd_2_0 := (Litex.number (M := M) (-3 : ℂ));
  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.div _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
  let _object_w19 := (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (_object_i3 (M := M)) _object_w18 _object_w19 (h_261 (M := M)) (by
    let _atomic_wd_1_0 := _object_w18
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((-3 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (_object_w18).val.left (Litex.number (M := M) (2 : ℂ)) (_object_w18).wd.1 (_object_w18).wd.2.1 (_object_w18).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-3 : ℂ) / (2 : ℂ)) ((-3 : ℝ) / (2 : ℝ)) (by norm_num)))) (by
    let _atomic_wd_1_0 := _object_w19
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((5 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_w19).wd.1 (_object_w19).wd.2.1 (_object_w19).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((5 : ℂ) / (2 : ℂ)) ((5 : ℝ) / (2 : ℝ)) (by norm_num)))) True.intro))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_327 (M := M))
      )
  )

theorem h_652 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _object_w18 := (let _wd_2_0 := (Litex.number (M := M) (-3 : ℂ));
  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.div _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
  let _object_w19 := (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (_object_i3 (M := M)) _object_w18 _object_w19 (h_261 (M := M)) (by
    let _atomic_wd_1_0 := _object_w18
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((-3 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (_object_w18).val.left (Litex.number (M := M) (2 : ℂ)) (_object_w18).wd.1 (_object_w18).wd.2.1 (_object_w18).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-3 : ℂ) / (2 : ℂ)) ((-3 : ℝ) / (2 : ℝ)) (by norm_num)))) (by
    let _atomic_wd_1_0 := _object_w19
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((5 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_w19).wd.1 (_object_w19).wd.2.1 (_object_w19).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((5 : ℂ) / (2 : ℂ)) ((5 : ℝ) / (2 : ℝ)) (by norm_num)))) True.intro));
  let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  (Litex.add _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.realToComplex (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (_object_i3 (M := M)) (let _wd_1_0 := (Litex.number (M := M) (-3 : ℂ));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) (h_261 (M := M)) (by
      let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (-3 : ℂ));
      let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
      (Litex.div _wd_1_0 _wd_1_1 (by
        let _atomic_wd_1_0 := _wd_1_0
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((-3 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (-3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (by
        let _atomic_wd_1_0 := (Litex.number (M := M) (-3 : ℂ))
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-3 : ℂ) / (2 : ℂ)) ((-3 : ℝ) / (2 : ℝ)) (by norm_num)))) (by
      let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((5 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((5 : ℂ) / (2 : ℂ)) ((5 : ℝ) / (2 : ℝ)) (by norm_num)))) True.intro) (Litex.call2InOutput (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (_object_i3 (M := M)) (let _wd_1_0 := (Litex.number (M := M) (-3 : ℂ));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) (h_261 (M := M)) (by
      let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (-3 : ℂ));
      let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
      (Litex.div _wd_1_0 _wd_1_1 (by
        let _atomic_wd_1_0 := _wd_1_0
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((-3 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (-3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (by
        let _atomic_wd_1_0 := (Litex.number (M := M) (-3 : ℂ))
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-3 : ℂ) / (2 : ℂ)) ((-3 : ℝ) / (2 : ℝ)) (by norm_num)))) (by
      let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((5 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((5 : ℂ) / (2 : ℂ)) ((5 : ℝ) / (2 : ℝ)) (by norm_num)))) True.intro)))) (by
    let _atomic_wd_1_0 := _wd_2_1
    exact (Litex.divInC (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2))));
  (Litex.floor _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (by
      let _litex_real_result := _atomic_wd_1_0
      exact Litex.addInR _litex_real_result.val.left _litex_real_result.val.right (by
      let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
      exact (by
        let _litex_return_call := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (_object_i3 (M := M)) (let _wd_1_0 := (Litex.number (M := M) (-3 : ℂ));
      let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
      (Litex.div _wd_1_0 _wd_1_1 (by
        let _atomic_wd_1_0 := _wd_1_0
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) (h_261 (M := M)) (by
        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (-3 : ℂ));
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.div _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((-3 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (-3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (by
          let _atomic_wd_1_0 := (Litex.number (M := M) (-3 : ℂ))
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-3 : ℂ) / (2 : ℂ)) ((-3 : ℝ) / (2 : ℝ)) (by norm_num)))) (by
        let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((5 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((5 : ℂ) / (2 : ℂ)) ((5 : ℝ) / (2 : ℝ)) (by norm_num)))) True.intro)
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) (by
      let _atomic_wd_2_0 := (_atomic_wd_1_0).val.right
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℝ) / (3 : ℝ)) (by norm_num))))
    ))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _object_w18 := (let _wd_2_0 := (Litex.number (M := M) (-3 : ℂ));
        let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.div _wd_2_0 _wd_2_1 (by
          let _atomic_wd_1_0 := _wd_2_0
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
        let _object_w19 := (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (_object_i3 (M := M)) _object_w18 _object_w19 (h_261 (M := M)) (by
          let _atomic_wd_1_0 := _object_w18
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((-3 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (_object_w18).val.left (Litex.number (M := M) (2 : ℂ)) (_object_w18).wd.1 (_object_w18).wd.2.1 (_object_w18).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-3 : ℂ) / (2 : ℂ)) ((-3 : ℝ) / (2 : ℝ)) (by norm_num)))) (by
          let _atomic_wd_1_0 := _object_w19
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((5 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_w19).wd.1 (_object_w19).wd.2.1 (_object_w19).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((5 : ℂ) / (2 : ℂ)) ((5 : ℝ) / (2 : ℝ)) (by norm_num)))) True.intro));
        let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        (Litex.add _wd_2_0 _wd_2_1 (by
          let _atomic_wd_1_0 := _wd_2_0
          exact (Litex.realToComplex (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (_object_i3 (M := M)) (let _wd_1_0 := (Litex.number (M := M) (-3 : ℂ));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) (h_261 (M := M)) (by
            let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (-3 : ℂ));
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.div _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((-3 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (-3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (by
              let _atomic_wd_1_0 := (Litex.number (M := M) (-3 : ℂ))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-3 : ℂ) / (2 : ℂ)) ((-3 : ℝ) / (2 : ℝ)) (by norm_num)))) (by
            let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((5 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((5 : ℂ) / (2 : ℂ)) ((5 : ℝ) / (2 : ℝ)) (by norm_num)))) True.intro) (Litex.call2InOutput (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (_object_i3 (M := M)) (let _wd_1_0 := (Litex.number (M := M) (-3 : ℂ));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) (h_261 (M := M)) (by
            let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (-3 : ℂ));
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.div _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((-3 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (-3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (by
              let _atomic_wd_1_0 := (Litex.number (M := M) (-3 : ℂ))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-3 : ℂ) / (2 : ℂ)) ((-3 : ℝ) / (2 : ℝ)) (by norm_num)))) (by
            let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((5 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((5 : ℂ) / (2 : ℂ)) ((5 : ℝ) / (2 : ℝ)) (by norm_num)))) True.intro)))) (by
          let _atomic_wd_1_0 := _wd_2_1
          exact (Litex.divInC (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2))));
        (Litex.floor _wd_1_0 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (by
            let _litex_real_result := _atomic_wd_1_0
            exact Litex.addInR _litex_real_result.val.left _litex_real_result.val.right (by
            let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
            exact (by
              let _litex_return_call := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (_object_i3 (M := M)) (let _wd_1_0 := (Litex.number (M := M) (-3 : ℂ));
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.div _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := _wd_1_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) (h_261 (M := M)) (by
              let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (-3 : ℂ));
              let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
              (Litex.div _wd_1_0 _wd_1_1 (by
                let _atomic_wd_1_0 := _wd_1_0
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((-3 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (-3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (by
                let _atomic_wd_1_0 := (Litex.number (M := M) (-3 : ℂ))
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-3 : ℂ) / (2 : ℂ)) ((-3 : ℝ) / (2 : ℝ)) (by norm_num)))) (by
              let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((5 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((5 : ℂ) / (2 : ℂ)) ((5 : ℝ) / (2 : ℝ)) (by norm_num)))) True.intro)
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) (by
            let _atomic_wd_2_0 := (_atomic_wd_1_0).val.right
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℝ) / (3 : ℝ)) (by norm_num))))
          ))));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from ((show Litex.denote _equal_wd_1_0 = M.number (2 : ℂ) from by simpa only [M.neg_numbers] using ((congrArg (Litex.roundingValue (M := M) false) (congrArg₂ M.addValue (h_327 (M := M)) (Eq.refl (M.divValue (M.number (1 : ℂ)) (M.number (3 : ℂ))))))).trans (show ((Litex.roundingValue (M := M) false) (M.addValue (M.number (2 : ℂ)) (M.divValue (M.number (1 : ℂ)) (M.number (3 : ℂ))))) = M.number (2 : ℂ) from (congrArg (Litex.roundingValue (M := M) false) (show (M.addValue (M.number (2 : ℂ)) (M.divValue (M.number (1 : ℂ)) (M.number (3 : ℂ)))) = M.number ((7 : ℂ) / (3 : ℂ)) from ((congrArg₂ M.addValue (show (M.number (2 : ℂ)) = M.number (2 : ℂ) from (congrArg M.number (show (2 : ℂ) = (2 : ℂ) from by norm_num))) (show (M.divValue (M.number (1 : ℂ)) (M.number (3 : ℂ))) = M.number ((1 : ℂ) / (3 : ℂ)) from ((congrArg₂ M.divValue (show (M.number (1 : ℂ)) = M.number (1 : ℂ) from (congrArg M.number (show (1 : ℂ) = (1 : ℂ) from by norm_num))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans ((M.div_numbers (1 : ℂ) (3 : ℂ) (by norm_num)).trans (congrArg M.number (by norm_num)))))).trans ((M.add_numbers (2 : ℂ) ((1 : ℂ) / (3 : ℂ))).trans (congrArg M.number (by norm_num)))))).trans (by
          have _numeric := Litex.roundingValue_number false (M := M) ((7 : ℝ) / (3 : ℝ))
          norm_num [Real.sign] at _numeric
          simpa only [neg_div] using _numeric)))).trans (((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))).symm)))
      )
  )

theorem h_943 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (let _object_w18 := (let _wd_2_0 := (Litex.number (M := M) (-3 : ℂ));
  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.div _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_2_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))));
  let _object_w19 := (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (_object_i3 (M := M)) _object_w18 _object_w19 (h_261 (M := M)) (by
    let _atomic_wd_1_0 := _object_w18
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((-3 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (_object_w18).val.left (Litex.number (M := M) (2 : ℂ)) (_object_w18).wd.1 (_object_w18).wd.2.1 (_object_w18).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-3 : ℂ) / (2 : ℂ)) ((-3 : ℝ) / (2 : ℝ)) (by norm_num)))) (by
    let _atomic_wd_1_0 := _object_w19
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((5 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_w19).wd.1 (_object_w19).wd.2.1 (_object_w19).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((5 : ℂ) / (2 : ℂ)) ((5 : ℝ) / (2 : ℝ)) (by norm_num)))) True.intro));
  let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  (Litex.add _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := _wd_2_0
    exact (Litex.realToComplex (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (_object_i3 (M := M)) (let _wd_1_0 := (Litex.number (M := M) (-3 : ℂ));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) (h_261 (M := M)) (by
      let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (-3 : ℂ));
      let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
      (Litex.div _wd_1_0 _wd_1_1 (by
        let _atomic_wd_1_0 := _wd_1_0
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((-3 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (-3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (by
        let _atomic_wd_1_0 := (Litex.number (M := M) (-3 : ℂ))
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-3 : ℂ) / (2 : ℂ)) ((-3 : ℝ) / (2 : ℝ)) (by norm_num)))) (by
      let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((5 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((5 : ℂ) / (2 : ℂ)) ((5 : ℝ) / (2 : ℝ)) (by norm_num)))) True.intro) (Litex.call2InOutput (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (_object_i3 (M := M)) (let _wd_1_0 := (Litex.number (M := M) (-3 : ℂ));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.div _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) (h_261 (M := M)) (by
      let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (-3 : ℂ));
      let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
      (Litex.div _wd_1_0 _wd_1_1 (by
        let _atomic_wd_1_0 := _wd_1_0
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((-3 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (-3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (by
        let _atomic_wd_1_0 := (Litex.number (M := M) (-3 : ℂ))
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-3 : ℂ) / (2 : ℂ)) ((-3 : ℝ) / (2 : ℝ)) (by norm_num)))) (by
      let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((5 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((5 : ℂ) / (2 : ℂ)) ((5 : ℝ) / (2 : ℝ)) (by norm_num)))) True.intro)))) (by
    let _atomic_wd_1_0 := _wd_2_1
    exact (Litex.divInC (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2))));
  (Litex.floor _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (by
      let _litex_real_result := _atomic_wd_1_0
      exact Litex.addInR _litex_real_result.val.left _litex_real_result.val.right (by
      let _atomic_wd_2_0 := (_atomic_wd_1_0).val.left
      exact (by
        let _litex_return_call := (Litex.call2 Litex.StandardSetValue.real Litex.StandardSetValue.real Litex.StandardSetValue.real (fun (_raw_i4 : M.Value) (_raw_i5 : M.Value) => True) (_object_i3 (M := M)) (let _wd_1_0 := (Litex.number (M := M) (-3 : ℂ));
      let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
      (Litex.div _wd_1_0 _wd_1_1 (by
        let _atomic_wd_1_0 := _wd_1_0
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))) (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))) (h_261 (M := M)) (by
        let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.number (M := M) (-3 : ℂ));
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.div _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((-3 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (-3 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (by
          let _atomic_wd_1_0 := (Litex.number (M := M) (-3 : ℂ))
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (-3 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))) (Litex.numberInC (M := M) (-3 : ℂ)))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((-3 : ℂ) / (2 : ℂ)) ((-3 : ℝ) / (2 : ℝ)) (by norm_num)))) (by
        let _atomic_wd_1_0 := (Litex.div (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((5 : ℂ) / (2 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInROfEq ((5 : ℂ) / (2 : ℂ)) ((5 : ℝ) / (2 : ℝ)) (by norm_num)))) True.intro)
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.call2InOutput _litex_return_call))) (by
      let _atomic_wd_2_0 := (_atomic_wd_1_0).val.right
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInROfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℝ) / (3 : ℝ)) (by norm_num))))
    ))))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_652 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_real_x5f_functions_x2f_statement_x2e_lit
