import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_rational_x5f_fold_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_18897 : (by
  let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  (let _setElement_0 := _wd_2_0;
    let _setElement_1 := _wd_2_1;
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
      let _atomic_wd_1_0 := _wd_2_0
      let _atomic_wd_1_1 := _wd_2_1
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _atomic_wd_1_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_1).wd.1 (_atomic_wd_1_1).wd.2.1 (_atomic_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0));
  let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
    intro _raw_i1 h_18924 _
    let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_18924)
    have h_18924 : Litex.In _value_i1 (Litex.Q (M := M)) := h_18924
    change Litex.In _value_i1 (Litex.Q (M := M))
    exact h_18924));
  let _wd_1_2 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
    intro _raw_i2 _raw_i3 h_18943 h_18944 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_18943)
    have h_18943 : Litex.In _value_i2 (Litex.Q (M := M)) := h_18943
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_18944)
    have h_18944 : Litex.In _value_i3 (Litex.Q (M := M)) := h_18944
    change (by
      let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_18943) (Litex.rationalToComplex _value_i3 h_18944))
      exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_18943) (Litex.rationalToComplex _value_i3 h_18944))
      exact (Litex.mulInQ _value_i2 _value_i3 h_18943 h_18944))));
  let _wd_1_3 := (Litex.number (M := M) (2 : ℂ));
  (let h_19022 : (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
    let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
    (let _setElement_0 := _wd_2_0;
      let _setElement_1 := _wd_2_1;
      let _setTail_2 := Litex.emptySet (M := M);
      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
        let _atomic_wd_2_0 := _wd_2_0
        let _atomic_wd_2_1 := _wd_2_1
        exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0))
    exact Litex.IsFiniteSet _atomic_wd_1_0) := (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
    let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
    (let _setElement_0 := _wd_2_0;
      let _setElement_1 := _wd_2_1;
      let _setTail_2 := Litex.emptySet (M := M);
      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
        let _atomic_wd_2_0 := _wd_2_0
        let _atomic_wd_2_1 := _wd_2_1
        exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0))
    exact (let _finite_tail_0 := _atomic_wd_1_0;
    let _finite_tail_1 := _finite_tail_0.val.tail;
    let _finite_tail_2 := _finite_tail_1.val.tail;
    have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
    have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
    have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
    _finite_0));
  let h_19036 : Litex.In _wd_1_3 (Litex.Q (M := M)) := (Litex.NativeBridge.numberInQOfEq (M := M) (2 : ℂ) (2 : ℚ) (by norm_num));
  let h_19041 : ∀ {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_19054 : Litex.In _value_i10 (Litex.Q (M := M))) {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_19055 : Litex.In _value_i11 (Litex.Q (M := M))), (by
    let _object_w48 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
      intro _raw_i2 _raw_i3 h_19069 h_19070 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_19069)
      have h_19069 : Litex.In _value_i2 (Litex.Q (M := M)) := h_19069
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_19070)
      have h_19070 : Litex.In _value_i3 (Litex.Q (M := M)) := h_19070
      change (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_19069) (Litex.rationalToComplex _value_i3 h_19070))
        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_19069) (Litex.rationalToComplex _value_i3 h_19070))
        exact (Litex.mulInQ _value_i2 _value_i3 h_19069 h_19070))));
    let _wd_2_1 := _value_i10;
    let _wd_2_2 := _value_i11;
    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_19054 h_19055 True.intro))
    let _object_w49 := (Litex.mul _value_i10 _value_i11 (Litex.rationalToComplex _value_i10 h_19054) (Litex.rationalToComplex _value_i11 h_19055))
    let _object_w50 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
      intro _raw_i2 _raw_i3 h_20545 h_20546 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_20545)
      have h_20545 : Litex.In _value_i2 (Litex.Q (M := M)) := h_20545
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_20546)
      have h_20546 : Litex.In _value_i3 (Litex.Q (M := M)) := h_20546
      change (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_20545) (Litex.rationalToComplex _value_i3 h_20546))
        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_20545) (Litex.rationalToComplex _value_i3 h_20546))
        exact (Litex.mulInQ _value_i2 _value_i3 h_20545 h_20546))));
    let _wd_2_1 := _value_i11;
    let _wd_2_2 := _value_i10;
    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_19055 h_19054 True.intro))
    let _object_w51 := (Litex.mul _value_i11 _value_i10 (Litex.rationalToComplex _value_i11 h_19055) (Litex.rationalToComplex _value_i10 h_19054))
    exact (((by
      let _equal_wd_2_0 := _object_w48
      let _equal_wd_2_1 := _object_w49
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
      let _equal_wd_2_0 := _object_w50
      let _equal_wd_2_1 := _object_w51
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
      let _equal_wd_2_0 := _object_w49
      let _equal_wd_2_1 := _object_w51
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((by
      let _equal_wd_2_0 := _object_w48
      let _equal_wd_2_1 := _object_w50
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)))))))
  ) := (by
    intro _Host_i10 _rep_i10 _value_i10 h_19054 _Host_i11 _rep_i11 _value_i11 h_19055
    let _object_w48 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
      intro _raw_i2 _raw_i3 h_19069 h_19070 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_19069)
      have h_19069 : Litex.In _value_i2 (Litex.Q (M := M)) := h_19069
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_19070)
      have h_19070 : Litex.In _value_i3 (Litex.Q (M := M)) := h_19070
      change (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_19069) (Litex.rationalToComplex _value_i3 h_19070))
        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_19069) (Litex.rationalToComplex _value_i3 h_19070))
        exact (Litex.mulInQ _value_i2 _value_i3 h_19069 h_19070))));
    let _wd_2_1 := _value_i10;
    let _wd_2_2 := _value_i11;
    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_19054 h_19055 True.intro))
    let _object_w49 := (Litex.mul _value_i10 _value_i11 (Litex.rationalToComplex _value_i10 h_19054) (Litex.rationalToComplex _value_i11 h_19055))
    have h_19037 : (by
      let _equal_wd_2_0 := _object_w48
      let _equal_wd_2_1 := _object_w49
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])) = (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) from by
              have _litex_residual : (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) = (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])) = (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) from by
              let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                intro _raw_i2 _raw_i3 h_20196 h_20197 _
                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_20196)
                have h_20196 : Litex.In _value_i2 (Litex.Q (M := M)) := h_20196
                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_20197)
                have h_20197 : Litex.In _value_i3 (Litex.Q (M := M)) := h_20197
                change (by
                  let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_20196) (Litex.rationalToComplex _value_i3 h_20197))
                  exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                exact (by
                  let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_20196) (Litex.rationalToComplex _value_i3 h_20197))
                  exact (Litex.mulInQ _value_i2 _value_i3 h_20196 h_20197))));
              let _wd_2_1 := _value_i10;
              let _wd_2_2 := _value_i11;
              (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_19054 h_19055 True.intro))
              let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                intro _raw_i2 _raw_i3 h_20339 h_20340 _
                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_20339)
                have h_20339 : Litex.In _value_i2 (Litex.Q (M := M)) := h_20339
                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_20340)
                have h_20340 : Litex.In _value_i3 (Litex.Q (M := M)) := h_20340
                change (by
                  let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_20339) (Litex.rationalToComplex _value_i3 h_20340))
                  exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                exact (by
                  let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_20339) (Litex.rationalToComplex _value_i3 h_20340))
                  exact (Litex.mulInQ _value_i2 _value_i3 h_20339 h_20340))));
              let _wd_2_1 := _value_i10;
              let _wd_2_2 := _value_i11;
              (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_19054 h_19055 True.intro))
              have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
              have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) from rfl))
            ))).trans _litex_residual)
          )
      )
    let _object_w50 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
      intro _raw_i2 _raw_i3 h_20545 h_20546 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_20545)
      have h_20545 : Litex.In _value_i2 (Litex.Q (M := M)) := h_20545
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_20546)
      have h_20546 : Litex.In _value_i3 (Litex.Q (M := M)) := h_20546
      change (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_20545) (Litex.rationalToComplex _value_i3 h_20546))
        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_20545) (Litex.rationalToComplex _value_i3 h_20546))
        exact (Litex.mulInQ _value_i2 _value_i3 h_20545 h_20546))));
    let _wd_2_1 := _value_i11;
    let _wd_2_2 := _value_i10;
    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_19055 h_19054 True.intro))
    let _object_w51 := (Litex.mul _value_i11 _value_i10 (Litex.rationalToComplex _value_i11 h_19055) (Litex.rationalToComplex _value_i10 h_19054))
    have h_19038 : (by
      let _equal_wd_2_0 := _object_w50
      let _equal_wd_2_1 := _object_w51
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i11), (Litex.denote _value_i10)])) = (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i10)) from by
              have _litex_residual : (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i10)) = (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i10)) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i11), (Litex.denote _value_i10)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i11), (Litex.denote _value_i10)])) = (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i10)) from by
              let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                intro _raw_i2 _raw_i3 h_21672 h_21673 _
                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_21672)
                have h_21672 : Litex.In _value_i2 (Litex.Q (M := M)) := h_21672
                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_21673)
                have h_21673 : Litex.In _value_i3 (Litex.Q (M := M)) := h_21673
                change (by
                  let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_21672) (Litex.rationalToComplex _value_i3 h_21673))
                  exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                exact (by
                  let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_21672) (Litex.rationalToComplex _value_i3 h_21673))
                  exact (Litex.mulInQ _value_i2 _value_i3 h_21672 h_21673))));
              let _wd_2_1 := _value_i11;
              let _wd_2_2 := _value_i10;
              (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_19055 h_19054 True.intro))
              let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                intro _raw_i2 _raw_i3 h_21815 h_21816 _
                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_21815)
                have h_21815 : Litex.In _value_i2 (Litex.Q (M := M)) := h_21815
                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_21816)
                have h_21816 : Litex.In _value_i3 (Litex.Q (M := M)) := h_21816
                change (by
                  let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_21815) (Litex.rationalToComplex _value_i3 h_21816))
                  exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                exact (by
                  let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_21815) (Litex.rationalToComplex _value_i3 h_21816))
                  exact (Litex.mulInQ _value_i2 _value_i3 h_21815 h_21816))));
              let _wd_2_1 := _value_i11;
              let _wd_2_2 := _value_i10;
              (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_19055 h_19054 True.intro))
              have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
              have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i10)) from rfl))
            ))).trans _litex_residual)
          )
      )
    have h_19039 : (by
      let _equal_wd_2_0 := _object_w49
      let _equal_wd_2_1 := _object_w51
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i10 (Litex.rationalToComplex _value_i10 h_19054)) * (Litex.NativeBridge.asComplex _value_i11 (Litex.rationalToComplex _value_i11 h_19055))) ((Litex.NativeBridge.asComplex _value_i11 (Litex.rationalToComplex _value_i11 h_19055)) * (Litex.NativeBridge.asComplex _value_i10 (Litex.rationalToComplex _value_i10 h_19054))) (Litex.NativeBridge.denoteMul _value_i10 _value_i11 (_object_w49).wd.1 (_object_w49).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.rationalToComplex _value_i10 h_19054)) (Litex.NativeBridge.asComplex_spec _value_i11 (Litex.rationalToComplex _value_i11 h_19055))) (Litex.NativeBridge.denoteMul _value_i11 _value_i10 (_object_w51).wd.1 (_object_w51).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i11 (Litex.rationalToComplex _value_i11 h_19055)) (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.rationalToComplex _value_i10 h_19054))) (by ring!))
          )
      )
    have h_19040 : (by
      let _equal_wd_2_0 := _object_w48
      let _equal_wd_2_1 := _object_w50
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            ((((h_19037).trans h_19039)).trans (h_19038).symm)
          )
      )
    exact (And.intro h_19037 (And.intro h_19038 (And.intro h_19039 h_19040)))
  );
  let h_22021 : ∀ {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_22034 : Litex.In _value_i10 (Litex.Q (M := M))) {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_22035 : Litex.In _value_i11 (Litex.Q (M := M))) {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_22036 : Litex.In _value_i12 (Litex.Q (M := M))), (by
    let _object_w53 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
      intro _raw_i2 _raw_i3 h_22050 h_22051 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_22050)
      have h_22050 : Litex.In _value_i2 (Litex.Q (M := M)) := h_22050
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_22051)
      have h_22051 : Litex.In _value_i3 (Litex.Q (M := M)) := h_22051
      change (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_22050) (Litex.rationalToComplex _value_i3 h_22051))
        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_22050) (Litex.rationalToComplex _value_i3 h_22051))
        exact (Litex.mulInQ _value_i2 _value_i3 h_22050 h_22051))));
    let _wd_2_1 := _value_i10;
    let _wd_2_2 := _value_i11;
    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22034 h_22035 True.intro))
    let _object_w54 := (Litex.mul _value_i10 _value_i11 (Litex.rationalToComplex _value_i10 h_22034) (Litex.rationalToComplex _value_i11 h_22035))
    let _object_w55 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
      intro _raw_i2 _raw_i3 h_23778 h_23779 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_23778)
      have h_23778 : Litex.In _value_i2 (Litex.Q (M := M)) := h_23778
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_23779)
      have h_23779 : Litex.In _value_i3 (Litex.Q (M := M)) := h_23779
      change (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_23778) (Litex.rationalToComplex _value_i3 h_23779))
        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_23778) (Litex.rationalToComplex _value_i3 h_23779))
        exact (Litex.mulInQ _value_i2 _value_i3 h_23778 h_23779))));
    let _wd_2_1 := _value_i11;
    let _wd_2_2 := _value_i12;
    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22035 h_22036 True.intro))
    let _object_w56 := (Litex.mul _value_i11 _value_i12 (Litex.rationalToComplex _value_i11 h_22035) (Litex.rationalToComplex _value_i12 h_22036))
    let _object_w57 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
      intro _raw_i2 _raw_i3 h_25542 h_25543 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_25542)
      have h_25542 : Litex.In _value_i2 (Litex.Q (M := M)) := h_25542
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_25543)
      have h_25543 : Litex.In _value_i3 (Litex.Q (M := M)) := h_25543
      change (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25542) (Litex.rationalToComplex _value_i3 h_25543))
        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25542) (Litex.rationalToComplex _value_i3 h_25543))
        exact (Litex.mulInQ _value_i2 _value_i3 h_25542 h_25543))));
    let _wd_2_1 := _object_w53;
    let _wd_2_2 := _value_i12;
    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
      let _atomic_wd_1_0 := _object_w53
      exact (Litex.inOfSame _object_w53 _object_w53 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w53) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w53))) h_22036 True.intro))
    let _object_w58 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
      intro _raw_i2 _raw_i3 h_25756 h_25757 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_25756)
      have h_25756 : Litex.In _value_i2 (Litex.Q (M := M)) := h_25756
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_25757)
      have h_25757 : Litex.In _value_i3 (Litex.Q (M := M)) := h_25757
      change (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25756) (Litex.rationalToComplex _value_i3 h_25757))
        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25756) (Litex.rationalToComplex _value_i3 h_25757))
        exact (Litex.mulInQ _value_i2 _value_i3 h_25756 h_25757))));
    let _wd_2_1 := _object_w54;
    let _wd_2_2 := _value_i12;
    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
      let _atomic_wd_1_0 := _object_w54
      exact (Litex.mulInQ _value_i10 _value_i11 h_22034 h_22035)) h_22036 True.intro))
    let _object_w59 := (let _wd_2_0 := _object_w54;
    let _wd_2_1 := _value_i12;
    (Litex.mul _wd_2_0 _wd_2_1 (by
      let _atomic_wd_1_0 := _object_w54
      exact (Litex.mulInC _value_i10 _value_i11 (Litex.rationalToComplex _value_i10 h_22034) (Litex.rationalToComplex _value_i11 h_22035))) (Litex.rationalToComplex _wd_2_1 h_22036)))
    let _object_w60 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
      intro _raw_i2 _raw_i3 h_26880 h_26881 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_26880)
      have h_26880 : Litex.In _value_i2 (Litex.Q (M := M)) := h_26880
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_26881)
      have h_26881 : Litex.In _value_i3 (Litex.Q (M := M)) := h_26881
      change (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_26880) (Litex.rationalToComplex _value_i3 h_26881))
        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_26880) (Litex.rationalToComplex _value_i3 h_26881))
        exact (Litex.mulInQ _value_i2 _value_i3 h_26880 h_26881))));
    let _wd_2_1 := _value_i10;
    let _wd_2_2 := _object_w55;
    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22034 (by
      let _atomic_wd_1_0 := _object_w55
      exact (Litex.inOfSame _object_w55 _object_w55 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w55) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w55))) True.intro))
    let _object_w61 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
      intro _raw_i2 _raw_i3 h_27090 h_27091 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_27090)
      have h_27090 : Litex.In _value_i2 (Litex.Q (M := M)) := h_27090
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_27091)
      have h_27091 : Litex.In _value_i3 (Litex.Q (M := M)) := h_27091
      change (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_27090) (Litex.rationalToComplex _value_i3 h_27091))
        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_27090) (Litex.rationalToComplex _value_i3 h_27091))
        exact (Litex.mulInQ _value_i2 _value_i3 h_27090 h_27091))));
    let _wd_2_1 := _value_i10;
    let _wd_2_2 := _object_w56;
    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22034 (by
      let _atomic_wd_1_0 := _object_w56
      exact (Litex.mulInQ _value_i11 _value_i12 h_22035 h_22036)) True.intro))
    let _object_w62 := (let _wd_2_0 := _value_i10;
    let _wd_2_1 := _object_w56;
    (Litex.mul _wd_2_0 _wd_2_1 (Litex.rationalToComplex _wd_2_0 h_22034) (by
      let _atomic_wd_1_0 := _object_w56
      exact (Litex.mulInC _value_i11 _value_i12 (Litex.rationalToComplex _value_i11 h_22035) (Litex.rationalToComplex _value_i12 h_22036)))))
    exact (((by
      let _equal_wd_2_0 := _object_w53
      let _equal_wd_2_1 := _object_w54
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
      let _equal_wd_2_0 := _object_w55
      let _equal_wd_2_1 := _object_w56
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
      let _equal_wd_2_0 := _object_w57
      let _equal_wd_2_1 := _object_w58
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
      let _equal_wd_2_0 := _object_w58
      let _equal_wd_2_1 := _object_w59
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
      let _equal_wd_2_0 := _object_w60
      let _equal_wd_2_1 := _object_w61
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
      let _equal_wd_2_0 := _object_w61
      let _equal_wd_2_1 := _object_w62
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
      let _equal_wd_2_0 := _object_w59
      let _equal_wd_2_1 := _object_w62
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((by
      let _equal_wd_2_0 := _object_w57
      let _equal_wd_2_1 := _object_w60
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)))))))))))))))
  ) := (by
    intro _Host_i10 _rep_i10 _value_i10 h_22034 _Host_i11 _rep_i11 _value_i11 h_22035 _Host_i12 _rep_i12 _value_i12 h_22036
    let _object_w53 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
      intro _raw_i2 _raw_i3 h_22050 h_22051 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_22050)
      have h_22050 : Litex.In _value_i2 (Litex.Q (M := M)) := h_22050
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_22051)
      have h_22051 : Litex.In _value_i3 (Litex.Q (M := M)) := h_22051
      change (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_22050) (Litex.rationalToComplex _value_i3 h_22051))
        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_22050) (Litex.rationalToComplex _value_i3 h_22051))
        exact (Litex.mulInQ _value_i2 _value_i3 h_22050 h_22051))));
    let _wd_2_1 := _value_i10;
    let _wd_2_2 := _value_i11;
    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22034 h_22035 True.intro))
    let _object_w54 := (Litex.mul _value_i10 _value_i11 (Litex.rationalToComplex _value_i10 h_22034) (Litex.rationalToComplex _value_i11 h_22035))
    have h_22013 : (by
      let _equal_wd_2_0 := _object_w53
      let _equal_wd_2_1 := _object_w54
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])) = (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) from by
              have _litex_residual : (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) = (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])) = (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) from by
              let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                intro _raw_i2 _raw_i3 h_23373 h_23374 _
                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_23373)
                have h_23373 : Litex.In _value_i2 (Litex.Q (M := M)) := h_23373
                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_23374)
                have h_23374 : Litex.In _value_i3 (Litex.Q (M := M)) := h_23374
                change (by
                  let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_23373) (Litex.rationalToComplex _value_i3 h_23374))
                  exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                exact (by
                  let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_23373) (Litex.rationalToComplex _value_i3 h_23374))
                  exact (Litex.mulInQ _value_i2 _value_i3 h_23373 h_23374))));
              let _wd_2_1 := _value_i10;
              let _wd_2_2 := _value_i11;
              (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22034 h_22035 True.intro))
              let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                intro _raw_i2 _raw_i3 h_23536 h_23537 _
                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_23536)
                have h_23536 : Litex.In _value_i2 (Litex.Q (M := M)) := h_23536
                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_23537)
                have h_23537 : Litex.In _value_i3 (Litex.Q (M := M)) := h_23537
                change (by
                  let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_23536) (Litex.rationalToComplex _value_i3 h_23537))
                  exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                exact (by
                  let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_23536) (Litex.rationalToComplex _value_i3 h_23537))
                  exact (Litex.mulInQ _value_i2 _value_i3 h_23536 h_23537))));
              let _wd_2_1 := _value_i10;
              let _wd_2_2 := _value_i11;
              (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22034 h_22035 True.intro))
              have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
              have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) from rfl))
            ))).trans _litex_residual)
          )
      )
    let _object_w55 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
      intro _raw_i2 _raw_i3 h_23778 h_23779 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_23778)
      have h_23778 : Litex.In _value_i2 (Litex.Q (M := M)) := h_23778
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_23779)
      have h_23779 : Litex.In _value_i3 (Litex.Q (M := M)) := h_23779
      change (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_23778) (Litex.rationalToComplex _value_i3 h_23779))
        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_23778) (Litex.rationalToComplex _value_i3 h_23779))
        exact (Litex.mulInQ _value_i2 _value_i3 h_23778 h_23779))));
    let _wd_2_1 := _value_i11;
    let _wd_2_2 := _value_i12;
    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22035 h_22036 True.intro))
    let _object_w56 := (Litex.mul _value_i11 _value_i12 (Litex.rationalToComplex _value_i11 h_22035) (Litex.rationalToComplex _value_i12 h_22036))
    have h_22014 : (by
      let _equal_wd_2_0 := _object_w55
      let _equal_wd_2_1 := _object_w56
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i11), (Litex.denote _value_i12)])) = (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12)) from by
              have _litex_residual : (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12)) = (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12)) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i11), (Litex.denote _value_i12)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i11), (Litex.denote _value_i12)])) = (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12)) from by
              let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                intro _raw_i2 _raw_i3 h_25129 h_25130 _
                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_25129)
                have h_25129 : Litex.In _value_i2 (Litex.Q (M := M)) := h_25129
                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_25130)
                have h_25130 : Litex.In _value_i3 (Litex.Q (M := M)) := h_25130
                change (by
                  let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25129) (Litex.rationalToComplex _value_i3 h_25130))
                  exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                exact (by
                  let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25129) (Litex.rationalToComplex _value_i3 h_25130))
                  exact (Litex.mulInQ _value_i2 _value_i3 h_25129 h_25130))));
              let _wd_2_1 := _value_i11;
              let _wd_2_2 := _value_i12;
              (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22035 h_22036 True.intro))
              let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                intro _raw_i2 _raw_i3 h_25296 h_25297 _
                let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_25296)
                have h_25296 : Litex.In _value_i2 (Litex.Q (M := M)) := h_25296
                let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_25297)
                have h_25297 : Litex.In _value_i3 (Litex.Q (M := M)) := h_25297
                change (by
                  let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25296) (Litex.rationalToComplex _value_i3 h_25297))
                  exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                exact (by
                  let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25296) (Litex.rationalToComplex _value_i3 h_25297))
                  exact (Litex.mulInQ _value_i2 _value_i3 h_25296 h_25297))));
              let _wd_2_1 := _value_i11;
              let _wd_2_2 := _value_i12;
              (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22035 h_22036 True.intro))
              have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
              have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12)) from rfl))
            ))).trans _litex_residual)
          )
      )
    let _object_w57 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
      intro _raw_i2 _raw_i3 h_25542 h_25543 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_25542)
      have h_25542 : Litex.In _value_i2 (Litex.Q (M := M)) := h_25542
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_25543)
      have h_25543 : Litex.In _value_i3 (Litex.Q (M := M)) := h_25543
      change (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25542) (Litex.rationalToComplex _value_i3 h_25543))
        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25542) (Litex.rationalToComplex _value_i3 h_25543))
        exact (Litex.mulInQ _value_i2 _value_i3 h_25542 h_25543))));
    let _wd_2_1 := _object_w53;
    let _wd_2_2 := _value_i12;
    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
      let _atomic_wd_1_0 := _object_w53
      exact (Litex.inOfSame _object_w53 _object_w53 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w53) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w53))) h_22036 True.intro))
    let _object_w58 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
      intro _raw_i2 _raw_i3 h_25756 h_25757 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_25756)
      have h_25756 : Litex.In _value_i2 (Litex.Q (M := M)) := h_25756
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_25757)
      have h_25757 : Litex.In _value_i3 (Litex.Q (M := M)) := h_25757
      change (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25756) (Litex.rationalToComplex _value_i3 h_25757))
        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25756) (Litex.rationalToComplex _value_i3 h_25757))
        exact (Litex.mulInQ _value_i2 _value_i3 h_25756 h_25757))));
    let _wd_2_1 := _object_w54;
    let _wd_2_2 := _value_i12;
    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
      let _atomic_wd_1_0 := _object_w54
      exact (Litex.mulInQ _value_i10 _value_i11 h_22034 h_22035)) h_22036 True.intro))
    have h_22015 : (by
      let _equal_wd_2_0 := _object_w57
      let _equal_wd_2_1 := _object_w58
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) h_22013 (show @Eq M.Value _ _ from Eq.refl _)))
          )
      )
    let _object_w59 := (let _wd_2_0 := _object_w54;
    let _wd_2_1 := _value_i12;
    (Litex.mul _wd_2_0 _wd_2_1 (by
      let _atomic_wd_1_0 := _object_w54
      exact (Litex.mulInC _value_i10 _value_i11 (Litex.rationalToComplex _value_i10 h_22034) (Litex.rationalToComplex _value_i11 h_22035))) (Litex.rationalToComplex _wd_2_1 h_22036)))
    have h_22016 : (by
      let _equal_wd_2_0 := _object_w58
      let _equal_wd_2_1 := _object_w59
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)), (Litex.denote _value_i12)])) = (M.mulValue (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) (Litex.denote _value_i12)) from by
              have _litex_residual : (M.mulValue (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) (Litex.denote _value_i12)) = (M.mulValue (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) (Litex.denote _value_i12)) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)), (Litex.denote _value_i12)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)), (Litex.denote _value_i12)])) = (M.mulValue (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) (Litex.denote _value_i12)) from by
              let _litex_original := _object_w58
              let _litex_literal := _object_w58
              have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
              have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) (Litex.denote _value_i12)) from rfl))
            ))).trans _litex_residual)
          )
      )
    let _object_w60 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
      intro _raw_i2 _raw_i3 h_26880 h_26881 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_26880)
      have h_26880 : Litex.In _value_i2 (Litex.Q (M := M)) := h_26880
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_26881)
      have h_26881 : Litex.In _value_i3 (Litex.Q (M := M)) := h_26881
      change (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_26880) (Litex.rationalToComplex _value_i3 h_26881))
        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_26880) (Litex.rationalToComplex _value_i3 h_26881))
        exact (Litex.mulInQ _value_i2 _value_i3 h_26880 h_26881))));
    let _wd_2_1 := _value_i10;
    let _wd_2_2 := _object_w55;
    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22034 (by
      let _atomic_wd_1_0 := _object_w55
      exact (Litex.inOfSame _object_w55 _object_w55 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w55) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w55))) True.intro))
    let _object_w61 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
      intro _raw_i2 _raw_i3 h_27090 h_27091 _
      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_27090)
      have h_27090 : Litex.In _value_i2 (Litex.Q (M := M)) := h_27090
      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_27091)
      have h_27091 : Litex.In _value_i3 (Litex.Q (M := M)) := h_27091
      change (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_27090) (Litex.rationalToComplex _value_i3 h_27091))
        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
      exact (by
        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_27090) (Litex.rationalToComplex _value_i3 h_27091))
        exact (Litex.mulInQ _value_i2 _value_i3 h_27090 h_27091))));
    let _wd_2_1 := _value_i10;
    let _wd_2_2 := _object_w56;
    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22034 (by
      let _atomic_wd_1_0 := _object_w56
      exact (Litex.mulInQ _value_i11 _value_i12 h_22035 h_22036)) True.intro))
    have h_22017 : (by
      let _equal_wd_2_0 := _object_w60
      let _equal_wd_2_1 := _object_w61
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_22014))
          )
      )
    let _object_w62 := (let _wd_2_0 := _value_i10;
    let _wd_2_1 := _object_w56;
    (Litex.mul _wd_2_0 _wd_2_1 (Litex.rationalToComplex _wd_2_0 h_22034) (by
      let _atomic_wd_1_0 := _object_w56
      exact (Litex.mulInC _value_i11 _value_i12 (Litex.rationalToComplex _value_i11 h_22035) (Litex.rationalToComplex _value_i12 h_22036)))))
    have h_22018 : (by
      let _equal_wd_2_0 := _object_w61
      let _equal_wd_2_1 := _object_w62
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12))])) = (M.mulValue (Litex.denote _value_i10) (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12))) from by
              have _litex_residual : (M.mulValue (Litex.denote _value_i10) (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12))) = (M.mulValue (Litex.denote _value_i10) (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12))) := (show @Eq M.Value _ _ from Eq.refl _)
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12))])) = (M.mulValue (Litex.denote _value_i10) (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12))) from by
              let _litex_original := _object_w61
              let _litex_literal := _object_w61
              have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
              have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
              exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i10) (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12))) from rfl))
            ))).trans _litex_residual)
          )
      )
    have h_22019 : (by
      let _equal_wd_2_0 := _object_w59
      let _equal_wd_2_1 := _object_w62
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i10 (Litex.rationalToComplex _value_i10 h_22034)) * (Litex.NativeBridge.asComplex _value_i11 (Litex.rationalToComplex _value_i11 h_22035))) * (Litex.NativeBridge.asComplex _value_i12 (Litex.rationalToComplex _value_i12 h_22036))) ((Litex.NativeBridge.asComplex _value_i10 (Litex.rationalToComplex _value_i10 h_22034)) * ((Litex.NativeBridge.asComplex _value_i11 (Litex.rationalToComplex _value_i11 h_22035)) * (Litex.NativeBridge.asComplex _value_i12 (Litex.rationalToComplex _value_i12 h_22036)))) (Litex.NativeBridge.denoteMul (_object_w59).val.left _value_i12 (_object_w59).wd.1 (_object_w59).wd.2 _ _ (Litex.NativeBridge.denoteMul _value_i10 _value_i11 (_object_w54).wd.1 (_object_w54).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.rationalToComplex _value_i10 h_22034)) (Litex.NativeBridge.asComplex_spec _value_i11 (Litex.rationalToComplex _value_i11 h_22035))) (Litex.NativeBridge.asComplex_spec _value_i12 (Litex.rationalToComplex _value_i12 h_22036))) (Litex.NativeBridge.denoteMul _value_i10 (_object_w62).val.right (_object_w62).wd.1 (_object_w62).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.rationalToComplex _value_i10 h_22034)) (Litex.NativeBridge.denoteMul _value_i11 _value_i12 (_object_w56).wd.1 (_object_w56).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i11 (Litex.rationalToComplex _value_i11 h_22035)) (Litex.NativeBridge.asComplex_spec _value_i12 (Litex.rationalToComplex _value_i12 h_22036)))) (by ring!))
          )
      )
    have h_22020 : (by
      let _equal_wd_2_0 := _object_w57
      let _equal_wd_2_1 := _object_w60
      exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
      (by
        litex_checked_step =>
          exact (
            ((((((((h_22015).trans h_22016)).trans h_22019)).trans (h_22018).symm)).trans (h_22017).symm)
          )
      )
    exact (And.intro h_22013 (And.intro h_22014 (And.intro h_22015 (And.intro h_22016 (And.intro h_22017 (And.intro h_22018 (And.intro h_22019 h_22020)))))))
  );
  let h_28204 : (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
    let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
    (let _setElement_0 := _wd_2_0;
      let _setElement_1 := _wd_2_1;
      let _setTail_2 := Litex.emptySet (M := M);
      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
        let _atomic_wd_2_0 := _wd_2_0
        let _atomic_wd_2_1 := _wd_2_1
        exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0))
    exact Litex.Subset _atomic_wd_1_0 (Litex.Q (M := M))) := (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
    let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
    (let _setElement_0 := _wd_2_0;
      let _setElement_1 := _wd_2_1;
      let _setTail_2 := Litex.emptySet (M := M);
      let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
      let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
      let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
        let _atomic_wd_2_0 := _wd_2_0
        let _atomic_wd_2_1 := _wd_2_1
        exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
      let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
      _setTail_0))
    exact (by
      let _set := _atomic_wd_1_0
      exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Q (M := M)) _set.wd (by
      let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℚ) / (2 : ℚ)) (by norm_num)))) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Q (M := M)) _set.val.tail.wd (by
      let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℚ) / (3 : ℚ)) (by norm_num)))) (Litex.emptySubset (Litex.Q (M := M)))))));
  Litex.finiteFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True)) h_19022 (Litex.formulaFnInFnSet _wd_1_1) (Litex.formulaFnInFnSet _wd_1_2) h_19036 (fun i hi => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.rational) (Litex.denote (Litex.Q (M := M))) (M.standard_isSet Litex.StandardSetValue.rational) (Litex.isSet (Litex.Q (M := M))) (fun (_raw_i1 : M.Value) => True) i).mpr ⟨h_28204 i hi, True.intro⟩) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x1 _fold_h1 => (And.right (And.right (And.right (h_19041 _fold_x0 _fold_h0 _fold_x1 _fold_h1)))))))) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x2 _fold_h2 => (And.right (And.right (And.right (And.right (And.right (And.right (And.right (h_22021 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2))))))))))))))))
  let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        (let _setElement_0 := _wd_2_0;
          let _setElement_1 := _wd_2_1;
          let _setTail_2 := Litex.emptySet (M := M);
          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
            let _atomic_wd_1_0 := _wd_2_0
            let _atomic_wd_1_1 := _wd_2_1
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _atomic_wd_1_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_1).wd.1 (_atomic_wd_1_1).wd.2.1 (_atomic_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0));
        let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
          intro _raw_i1 h_18924 _
          let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_18924)
          have h_18924 : Litex.In _value_i1 (Litex.Q (M := M)) := h_18924
          change Litex.In _value_i1 (Litex.Q (M := M))
          exact h_18924));
        let _wd_1_2 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
          intro _raw_i2 _raw_i3 h_18943 h_18944 _
          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_18943)
          have h_18943 : Litex.In _value_i2 (Litex.Q (M := M)) := h_18943
          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_18944)
          have h_18944 : Litex.In _value_i3 (Litex.Q (M := M)) := h_18944
          change (by
            let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_18943) (Litex.rationalToComplex _value_i3 h_18944))
            exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
          exact (by
            let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_18943) (Litex.rationalToComplex _value_i3 h_18944))
            exact (Litex.mulInQ _value_i2 _value_i3 h_18943 h_18944))));
        let _wd_1_3 := (Litex.number (M := M) (2 : ℂ));
        (let h_19022 : (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact Litex.IsFiniteSet _atomic_wd_1_0) := (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact (let _finite_tail_0 := _atomic_wd_1_0;
          let _finite_tail_1 := _finite_tail_0.val.tail;
          let _finite_tail_2 := _finite_tail_1.val.tail;
          have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
          have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
          have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
          _finite_0));
        let h_19036 : Litex.In _wd_1_3 (Litex.Q (M := M)) := (Litex.NativeBridge.numberInQOfEq (M := M) (2 : ℂ) (2 : ℚ) (by norm_num));
        let h_19041 : ∀ {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_19054 : Litex.In _value_i10 (Litex.Q (M := M))) {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_19055 : Litex.In _value_i11 (Litex.Q (M := M))), (by
          let _object_w48 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_19069 h_19070 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_19069)
            have h_19069 : Litex.In _value_i2 (Litex.Q (M := M)) := h_19069
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_19070)
            have h_19070 : Litex.In _value_i3 (Litex.Q (M := M)) := h_19070
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_19069) (Litex.rationalToComplex _value_i3 h_19070))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_19069) (Litex.rationalToComplex _value_i3 h_19070))
              exact (Litex.mulInQ _value_i2 _value_i3 h_19069 h_19070))));
          let _wd_2_1 := _value_i10;
          let _wd_2_2 := _value_i11;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_19054 h_19055 True.intro))
          let _object_w49 := (Litex.mul _value_i10 _value_i11 (Litex.rationalToComplex _value_i10 h_19054) (Litex.rationalToComplex _value_i11 h_19055))
          let _object_w50 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_20545 h_20546 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_20545)
            have h_20545 : Litex.In _value_i2 (Litex.Q (M := M)) := h_20545
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_20546)
            have h_20546 : Litex.In _value_i3 (Litex.Q (M := M)) := h_20546
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_20545) (Litex.rationalToComplex _value_i3 h_20546))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_20545) (Litex.rationalToComplex _value_i3 h_20546))
              exact (Litex.mulInQ _value_i2 _value_i3 h_20545 h_20546))));
          let _wd_2_1 := _value_i11;
          let _wd_2_2 := _value_i10;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_19055 h_19054 True.intro))
          let _object_w51 := (Litex.mul _value_i11 _value_i10 (Litex.rationalToComplex _value_i11 h_19055) (Litex.rationalToComplex _value_i10 h_19054))
          exact (((by
            let _equal_wd_2_0 := _object_w48
            let _equal_wd_2_1 := _object_w49
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
            let _equal_wd_2_0 := _object_w50
            let _equal_wd_2_1 := _object_w51
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
            let _equal_wd_2_0 := _object_w49
            let _equal_wd_2_1 := _object_w51
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((by
            let _equal_wd_2_0 := _object_w48
            let _equal_wd_2_1 := _object_w50
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)))))))
        ) := (by
          intro _Host_i10 _rep_i10 _value_i10 h_19054 _Host_i11 _rep_i11 _value_i11 h_19055
          let _object_w48 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_19069 h_19070 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_19069)
            have h_19069 : Litex.In _value_i2 (Litex.Q (M := M)) := h_19069
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_19070)
            have h_19070 : Litex.In _value_i3 (Litex.Q (M := M)) := h_19070
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_19069) (Litex.rationalToComplex _value_i3 h_19070))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_19069) (Litex.rationalToComplex _value_i3 h_19070))
              exact (Litex.mulInQ _value_i2 _value_i3 h_19069 h_19070))));
          let _wd_2_1 := _value_i10;
          let _wd_2_2 := _value_i11;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_19054 h_19055 True.intro))
          let _object_w49 := (Litex.mul _value_i10 _value_i11 (Litex.rationalToComplex _value_i10 h_19054) (Litex.rationalToComplex _value_i11 h_19055))
          have h_19037 : (by
            let _equal_wd_2_0 := _object_w48
            let _equal_wd_2_1 := _object_w49
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])) = (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) from by
                    have _litex_residual : (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) = (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])) = (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) from by
                    let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_20196 h_20197 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_20196)
                      have h_20196 : Litex.In _value_i2 (Litex.Q (M := M)) := h_20196
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_20197)
                      have h_20197 : Litex.In _value_i3 (Litex.Q (M := M)) := h_20197
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_20196) (Litex.rationalToComplex _value_i3 h_20197))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_20196) (Litex.rationalToComplex _value_i3 h_20197))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_20196 h_20197))));
                    let _wd_2_1 := _value_i10;
                    let _wd_2_2 := _value_i11;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_19054 h_19055 True.intro))
                    let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_20339 h_20340 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_20339)
                      have h_20339 : Litex.In _value_i2 (Litex.Q (M := M)) := h_20339
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_20340)
                      have h_20340 : Litex.In _value_i3 (Litex.Q (M := M)) := h_20340
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_20339) (Litex.rationalToComplex _value_i3 h_20340))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_20339) (Litex.rationalToComplex _value_i3 h_20340))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_20339 h_20340))));
                    let _wd_2_1 := _value_i10;
                    let _wd_2_2 := _value_i11;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_19054 h_19055 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          let _object_w50 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_20545 h_20546 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_20545)
            have h_20545 : Litex.In _value_i2 (Litex.Q (M := M)) := h_20545
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_20546)
            have h_20546 : Litex.In _value_i3 (Litex.Q (M := M)) := h_20546
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_20545) (Litex.rationalToComplex _value_i3 h_20546))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_20545) (Litex.rationalToComplex _value_i3 h_20546))
              exact (Litex.mulInQ _value_i2 _value_i3 h_20545 h_20546))));
          let _wd_2_1 := _value_i11;
          let _wd_2_2 := _value_i10;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_19055 h_19054 True.intro))
          let _object_w51 := (Litex.mul _value_i11 _value_i10 (Litex.rationalToComplex _value_i11 h_19055) (Litex.rationalToComplex _value_i10 h_19054))
          have h_19038 : (by
            let _equal_wd_2_0 := _object_w50
            let _equal_wd_2_1 := _object_w51
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i11), (Litex.denote _value_i10)])) = (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i10)) from by
                    have _litex_residual : (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i10)) = (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i10)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i11), (Litex.denote _value_i10)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i11), (Litex.denote _value_i10)])) = (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i10)) from by
                    let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_21672 h_21673 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_21672)
                      have h_21672 : Litex.In _value_i2 (Litex.Q (M := M)) := h_21672
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_21673)
                      have h_21673 : Litex.In _value_i3 (Litex.Q (M := M)) := h_21673
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_21672) (Litex.rationalToComplex _value_i3 h_21673))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_21672) (Litex.rationalToComplex _value_i3 h_21673))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_21672 h_21673))));
                    let _wd_2_1 := _value_i11;
                    let _wd_2_2 := _value_i10;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_19055 h_19054 True.intro))
                    let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_21815 h_21816 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_21815)
                      have h_21815 : Litex.In _value_i2 (Litex.Q (M := M)) := h_21815
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_21816)
                      have h_21816 : Litex.In _value_i3 (Litex.Q (M := M)) := h_21816
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_21815) (Litex.rationalToComplex _value_i3 h_21816))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_21815) (Litex.rationalToComplex _value_i3 h_21816))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_21815 h_21816))));
                    let _wd_2_1 := _value_i11;
                    let _wd_2_2 := _value_i10;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_19055 h_19054 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i10)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          have h_19039 : (by
            let _equal_wd_2_0 := _object_w49
            let _equal_wd_2_1 := _object_w51
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i10 (Litex.rationalToComplex _value_i10 h_19054)) * (Litex.NativeBridge.asComplex _value_i11 (Litex.rationalToComplex _value_i11 h_19055))) ((Litex.NativeBridge.asComplex _value_i11 (Litex.rationalToComplex _value_i11 h_19055)) * (Litex.NativeBridge.asComplex _value_i10 (Litex.rationalToComplex _value_i10 h_19054))) (Litex.NativeBridge.denoteMul _value_i10 _value_i11 (_object_w49).wd.1 (_object_w49).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.rationalToComplex _value_i10 h_19054)) (Litex.NativeBridge.asComplex_spec _value_i11 (Litex.rationalToComplex _value_i11 h_19055))) (Litex.NativeBridge.denoteMul _value_i11 _value_i10 (_object_w51).wd.1 (_object_w51).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i11 (Litex.rationalToComplex _value_i11 h_19055)) (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.rationalToComplex _value_i10 h_19054))) (by ring!))
                )
            )
          have h_19040 : (by
            let _equal_wd_2_0 := _object_w48
            let _equal_wd_2_1 := _object_w50
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  ((((h_19037).trans h_19039)).trans (h_19038).symm)
                )
            )
          exact (And.intro h_19037 (And.intro h_19038 (And.intro h_19039 h_19040)))
        );
        let h_22021 : ∀ {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_22034 : Litex.In _value_i10 (Litex.Q (M := M))) {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_22035 : Litex.In _value_i11 (Litex.Q (M := M))) {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_22036 : Litex.In _value_i12 (Litex.Q (M := M))), (by
          let _object_w53 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_22050 h_22051 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_22050)
            have h_22050 : Litex.In _value_i2 (Litex.Q (M := M)) := h_22050
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_22051)
            have h_22051 : Litex.In _value_i3 (Litex.Q (M := M)) := h_22051
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_22050) (Litex.rationalToComplex _value_i3 h_22051))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_22050) (Litex.rationalToComplex _value_i3 h_22051))
              exact (Litex.mulInQ _value_i2 _value_i3 h_22050 h_22051))));
          let _wd_2_1 := _value_i10;
          let _wd_2_2 := _value_i11;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22034 h_22035 True.intro))
          let _object_w54 := (Litex.mul _value_i10 _value_i11 (Litex.rationalToComplex _value_i10 h_22034) (Litex.rationalToComplex _value_i11 h_22035))
          let _object_w55 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_23778 h_23779 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_23778)
            have h_23778 : Litex.In _value_i2 (Litex.Q (M := M)) := h_23778
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_23779)
            have h_23779 : Litex.In _value_i3 (Litex.Q (M := M)) := h_23779
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_23778) (Litex.rationalToComplex _value_i3 h_23779))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_23778) (Litex.rationalToComplex _value_i3 h_23779))
              exact (Litex.mulInQ _value_i2 _value_i3 h_23778 h_23779))));
          let _wd_2_1 := _value_i11;
          let _wd_2_2 := _value_i12;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22035 h_22036 True.intro))
          let _object_w56 := (Litex.mul _value_i11 _value_i12 (Litex.rationalToComplex _value_i11 h_22035) (Litex.rationalToComplex _value_i12 h_22036))
          let _object_w57 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_25542 h_25543 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_25542)
            have h_25542 : Litex.In _value_i2 (Litex.Q (M := M)) := h_25542
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_25543)
            have h_25543 : Litex.In _value_i3 (Litex.Q (M := M)) := h_25543
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25542) (Litex.rationalToComplex _value_i3 h_25543))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25542) (Litex.rationalToComplex _value_i3 h_25543))
              exact (Litex.mulInQ _value_i2 _value_i3 h_25542 h_25543))));
          let _wd_2_1 := _object_w53;
          let _wd_2_2 := _value_i12;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
            let _atomic_wd_1_0 := _object_w53
            exact (Litex.inOfSame _object_w53 _object_w53 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w53) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w53))) h_22036 True.intro))
          let _object_w58 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_25756 h_25757 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_25756)
            have h_25756 : Litex.In _value_i2 (Litex.Q (M := M)) := h_25756
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_25757)
            have h_25757 : Litex.In _value_i3 (Litex.Q (M := M)) := h_25757
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25756) (Litex.rationalToComplex _value_i3 h_25757))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25756) (Litex.rationalToComplex _value_i3 h_25757))
              exact (Litex.mulInQ _value_i2 _value_i3 h_25756 h_25757))));
          let _wd_2_1 := _object_w54;
          let _wd_2_2 := _value_i12;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
            let _atomic_wd_1_0 := _object_w54
            exact (Litex.mulInQ _value_i10 _value_i11 h_22034 h_22035)) h_22036 True.intro))
          let _object_w59 := (let _wd_2_0 := _object_w54;
          let _wd_2_1 := _value_i12;
          (Litex.mul _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _object_w54
            exact (Litex.mulInC _value_i10 _value_i11 (Litex.rationalToComplex _value_i10 h_22034) (Litex.rationalToComplex _value_i11 h_22035))) (Litex.rationalToComplex _wd_2_1 h_22036)))
          let _object_w60 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_26880 h_26881 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_26880)
            have h_26880 : Litex.In _value_i2 (Litex.Q (M := M)) := h_26880
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_26881)
            have h_26881 : Litex.In _value_i3 (Litex.Q (M := M)) := h_26881
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_26880) (Litex.rationalToComplex _value_i3 h_26881))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_26880) (Litex.rationalToComplex _value_i3 h_26881))
              exact (Litex.mulInQ _value_i2 _value_i3 h_26880 h_26881))));
          let _wd_2_1 := _value_i10;
          let _wd_2_2 := _object_w55;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22034 (by
            let _atomic_wd_1_0 := _object_w55
            exact (Litex.inOfSame _object_w55 _object_w55 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w55) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w55))) True.intro))
          let _object_w61 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_27090 h_27091 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_27090)
            have h_27090 : Litex.In _value_i2 (Litex.Q (M := M)) := h_27090
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_27091)
            have h_27091 : Litex.In _value_i3 (Litex.Q (M := M)) := h_27091
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_27090) (Litex.rationalToComplex _value_i3 h_27091))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_27090) (Litex.rationalToComplex _value_i3 h_27091))
              exact (Litex.mulInQ _value_i2 _value_i3 h_27090 h_27091))));
          let _wd_2_1 := _value_i10;
          let _wd_2_2 := _object_w56;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22034 (by
            let _atomic_wd_1_0 := _object_w56
            exact (Litex.mulInQ _value_i11 _value_i12 h_22035 h_22036)) True.intro))
          let _object_w62 := (let _wd_2_0 := _value_i10;
          let _wd_2_1 := _object_w56;
          (Litex.mul _wd_2_0 _wd_2_1 (Litex.rationalToComplex _wd_2_0 h_22034) (by
            let _atomic_wd_1_0 := _object_w56
            exact (Litex.mulInC _value_i11 _value_i12 (Litex.rationalToComplex _value_i11 h_22035) (Litex.rationalToComplex _value_i12 h_22036)))))
          exact (((by
            let _equal_wd_2_0 := _object_w53
            let _equal_wd_2_1 := _object_w54
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
            let _equal_wd_2_0 := _object_w55
            let _equal_wd_2_1 := _object_w56
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
            let _equal_wd_2_0 := _object_w57
            let _equal_wd_2_1 := _object_w58
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
            let _equal_wd_2_0 := _object_w58
            let _equal_wd_2_1 := _object_w59
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
            let _equal_wd_2_0 := _object_w60
            let _equal_wd_2_1 := _object_w61
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
            let _equal_wd_2_0 := _object_w61
            let _equal_wd_2_1 := _object_w62
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
            let _equal_wd_2_0 := _object_w59
            let _equal_wd_2_1 := _object_w62
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((by
            let _equal_wd_2_0 := _object_w57
            let _equal_wd_2_1 := _object_w60
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)))))))))))))))
        ) := (by
          intro _Host_i10 _rep_i10 _value_i10 h_22034 _Host_i11 _rep_i11 _value_i11 h_22035 _Host_i12 _rep_i12 _value_i12 h_22036
          let _object_w53 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_22050 h_22051 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_22050)
            have h_22050 : Litex.In _value_i2 (Litex.Q (M := M)) := h_22050
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_22051)
            have h_22051 : Litex.In _value_i3 (Litex.Q (M := M)) := h_22051
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_22050) (Litex.rationalToComplex _value_i3 h_22051))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_22050) (Litex.rationalToComplex _value_i3 h_22051))
              exact (Litex.mulInQ _value_i2 _value_i3 h_22050 h_22051))));
          let _wd_2_1 := _value_i10;
          let _wd_2_2 := _value_i11;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22034 h_22035 True.intro))
          let _object_w54 := (Litex.mul _value_i10 _value_i11 (Litex.rationalToComplex _value_i10 h_22034) (Litex.rationalToComplex _value_i11 h_22035))
          have h_22013 : (by
            let _equal_wd_2_0 := _object_w53
            let _equal_wd_2_1 := _object_w54
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])) = (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) from by
                    have _litex_residual : (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) = (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])) = (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) from by
                    let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_23373 h_23374 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_23373)
                      have h_23373 : Litex.In _value_i2 (Litex.Q (M := M)) := h_23373
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_23374)
                      have h_23374 : Litex.In _value_i3 (Litex.Q (M := M)) := h_23374
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_23373) (Litex.rationalToComplex _value_i3 h_23374))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_23373) (Litex.rationalToComplex _value_i3 h_23374))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_23373 h_23374))));
                    let _wd_2_1 := _value_i10;
                    let _wd_2_2 := _value_i11;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22034 h_22035 True.intro))
                    let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_23536 h_23537 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_23536)
                      have h_23536 : Litex.In _value_i2 (Litex.Q (M := M)) := h_23536
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_23537)
                      have h_23537 : Litex.In _value_i3 (Litex.Q (M := M)) := h_23537
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_23536) (Litex.rationalToComplex _value_i3 h_23537))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_23536) (Litex.rationalToComplex _value_i3 h_23537))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_23536 h_23537))));
                    let _wd_2_1 := _value_i10;
                    let _wd_2_2 := _value_i11;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22034 h_22035 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          let _object_w55 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_23778 h_23779 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_23778)
            have h_23778 : Litex.In _value_i2 (Litex.Q (M := M)) := h_23778
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_23779)
            have h_23779 : Litex.In _value_i3 (Litex.Q (M := M)) := h_23779
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_23778) (Litex.rationalToComplex _value_i3 h_23779))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_23778) (Litex.rationalToComplex _value_i3 h_23779))
              exact (Litex.mulInQ _value_i2 _value_i3 h_23778 h_23779))));
          let _wd_2_1 := _value_i11;
          let _wd_2_2 := _value_i12;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22035 h_22036 True.intro))
          let _object_w56 := (Litex.mul _value_i11 _value_i12 (Litex.rationalToComplex _value_i11 h_22035) (Litex.rationalToComplex _value_i12 h_22036))
          have h_22014 : (by
            let _equal_wd_2_0 := _object_w55
            let _equal_wd_2_1 := _object_w56
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i11), (Litex.denote _value_i12)])) = (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12)) from by
                    have _litex_residual : (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12)) = (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i11), (Litex.denote _value_i12)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i11), (Litex.denote _value_i12)])) = (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12)) from by
                    let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_25129 h_25130 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_25129)
                      have h_25129 : Litex.In _value_i2 (Litex.Q (M := M)) := h_25129
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_25130)
                      have h_25130 : Litex.In _value_i3 (Litex.Q (M := M)) := h_25130
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25129) (Litex.rationalToComplex _value_i3 h_25130))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25129) (Litex.rationalToComplex _value_i3 h_25130))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_25129 h_25130))));
                    let _wd_2_1 := _value_i11;
                    let _wd_2_2 := _value_i12;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22035 h_22036 True.intro))
                    let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_25296 h_25297 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_25296)
                      have h_25296 : Litex.In _value_i2 (Litex.Q (M := M)) := h_25296
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_25297)
                      have h_25297 : Litex.In _value_i3 (Litex.Q (M := M)) := h_25297
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25296) (Litex.rationalToComplex _value_i3 h_25297))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25296) (Litex.rationalToComplex _value_i3 h_25297))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_25296 h_25297))));
                    let _wd_2_1 := _value_i11;
                    let _wd_2_2 := _value_i12;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22035 h_22036 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          let _object_w57 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_25542 h_25543 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_25542)
            have h_25542 : Litex.In _value_i2 (Litex.Q (M := M)) := h_25542
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_25543)
            have h_25543 : Litex.In _value_i3 (Litex.Q (M := M)) := h_25543
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25542) (Litex.rationalToComplex _value_i3 h_25543))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25542) (Litex.rationalToComplex _value_i3 h_25543))
              exact (Litex.mulInQ _value_i2 _value_i3 h_25542 h_25543))));
          let _wd_2_1 := _object_w53;
          let _wd_2_2 := _value_i12;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
            let _atomic_wd_1_0 := _object_w53
            exact (Litex.inOfSame _object_w53 _object_w53 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w53) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w53))) h_22036 True.intro))
          let _object_w58 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_25756 h_25757 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_25756)
            have h_25756 : Litex.In _value_i2 (Litex.Q (M := M)) := h_25756
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_25757)
            have h_25757 : Litex.In _value_i3 (Litex.Q (M := M)) := h_25757
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25756) (Litex.rationalToComplex _value_i3 h_25757))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25756) (Litex.rationalToComplex _value_i3 h_25757))
              exact (Litex.mulInQ _value_i2 _value_i3 h_25756 h_25757))));
          let _wd_2_1 := _object_w54;
          let _wd_2_2 := _value_i12;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
            let _atomic_wd_1_0 := _object_w54
            exact (Litex.mulInQ _value_i10 _value_i11 h_22034 h_22035)) h_22036 True.intro))
          have h_22015 : (by
            let _equal_wd_2_0 := _object_w57
            let _equal_wd_2_1 := _object_w58
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) h_22013 (show @Eq M.Value _ _ from Eq.refl _)))
                )
            )
          let _object_w59 := (let _wd_2_0 := _object_w54;
          let _wd_2_1 := _value_i12;
          (Litex.mul _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _object_w54
            exact (Litex.mulInC _value_i10 _value_i11 (Litex.rationalToComplex _value_i10 h_22034) (Litex.rationalToComplex _value_i11 h_22035))) (Litex.rationalToComplex _wd_2_1 h_22036)))
          have h_22016 : (by
            let _equal_wd_2_0 := _object_w58
            let _equal_wd_2_1 := _object_w59
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)), (Litex.denote _value_i12)])) = (M.mulValue (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) (Litex.denote _value_i12)) from by
                    have _litex_residual : (M.mulValue (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) (Litex.denote _value_i12)) = (M.mulValue (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) (Litex.denote _value_i12)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)), (Litex.denote _value_i12)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)), (Litex.denote _value_i12)])) = (M.mulValue (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) (Litex.denote _value_i12)) from by
                    let _litex_original := _object_w58
                    let _litex_literal := _object_w58
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) (Litex.denote _value_i12)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          let _object_w60 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_26880 h_26881 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_26880)
            have h_26880 : Litex.In _value_i2 (Litex.Q (M := M)) := h_26880
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_26881)
            have h_26881 : Litex.In _value_i3 (Litex.Q (M := M)) := h_26881
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_26880) (Litex.rationalToComplex _value_i3 h_26881))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_26880) (Litex.rationalToComplex _value_i3 h_26881))
              exact (Litex.mulInQ _value_i2 _value_i3 h_26880 h_26881))));
          let _wd_2_1 := _value_i10;
          let _wd_2_2 := _object_w55;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22034 (by
            let _atomic_wd_1_0 := _object_w55
            exact (Litex.inOfSame _object_w55 _object_w55 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w55) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w55))) True.intro))
          let _object_w61 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_27090 h_27091 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_27090)
            have h_27090 : Litex.In _value_i2 (Litex.Q (M := M)) := h_27090
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_27091)
            have h_27091 : Litex.In _value_i3 (Litex.Q (M := M)) := h_27091
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_27090) (Litex.rationalToComplex _value_i3 h_27091))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_27090) (Litex.rationalToComplex _value_i3 h_27091))
              exact (Litex.mulInQ _value_i2 _value_i3 h_27090 h_27091))));
          let _wd_2_1 := _value_i10;
          let _wd_2_2 := _object_w56;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22034 (by
            let _atomic_wd_1_0 := _object_w56
            exact (Litex.mulInQ _value_i11 _value_i12 h_22035 h_22036)) True.intro))
          have h_22017 : (by
            let _equal_wd_2_0 := _object_w60
            let _equal_wd_2_1 := _object_w61
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_22014))
                )
            )
          let _object_w62 := (let _wd_2_0 := _value_i10;
          let _wd_2_1 := _object_w56;
          (Litex.mul _wd_2_0 _wd_2_1 (Litex.rationalToComplex _wd_2_0 h_22034) (by
            let _atomic_wd_1_0 := _object_w56
            exact (Litex.mulInC _value_i11 _value_i12 (Litex.rationalToComplex _value_i11 h_22035) (Litex.rationalToComplex _value_i12 h_22036)))))
          have h_22018 : (by
            let _equal_wd_2_0 := _object_w61
            let _equal_wd_2_1 := _object_w62
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12))])) = (M.mulValue (Litex.denote _value_i10) (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12))) from by
                    have _litex_residual : (M.mulValue (Litex.denote _value_i10) (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12))) = (M.mulValue (Litex.denote _value_i10) (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12))])) = (M.mulValue (Litex.denote _value_i10) (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12))) from by
                    let _litex_original := _object_w61
                    let _litex_literal := _object_w61
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i10) (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12))) from rfl))
                  ))).trans _litex_residual)
                )
            )
          have h_22019 : (by
            let _equal_wd_2_0 := _object_w59
            let _equal_wd_2_1 := _object_w62
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i10 (Litex.rationalToComplex _value_i10 h_22034)) * (Litex.NativeBridge.asComplex _value_i11 (Litex.rationalToComplex _value_i11 h_22035))) * (Litex.NativeBridge.asComplex _value_i12 (Litex.rationalToComplex _value_i12 h_22036))) ((Litex.NativeBridge.asComplex _value_i10 (Litex.rationalToComplex _value_i10 h_22034)) * ((Litex.NativeBridge.asComplex _value_i11 (Litex.rationalToComplex _value_i11 h_22035)) * (Litex.NativeBridge.asComplex _value_i12 (Litex.rationalToComplex _value_i12 h_22036)))) (Litex.NativeBridge.denoteMul (_object_w59).val.left _value_i12 (_object_w59).wd.1 (_object_w59).wd.2 _ _ (Litex.NativeBridge.denoteMul _value_i10 _value_i11 (_object_w54).wd.1 (_object_w54).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.rationalToComplex _value_i10 h_22034)) (Litex.NativeBridge.asComplex_spec _value_i11 (Litex.rationalToComplex _value_i11 h_22035))) (Litex.NativeBridge.asComplex_spec _value_i12 (Litex.rationalToComplex _value_i12 h_22036))) (Litex.NativeBridge.denoteMul _value_i10 (_object_w62).val.right (_object_w62).wd.1 (_object_w62).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.rationalToComplex _value_i10 h_22034)) (Litex.NativeBridge.denoteMul _value_i11 _value_i12 (_object_w56).wd.1 (_object_w56).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i11 (Litex.rationalToComplex _value_i11 h_22035)) (Litex.NativeBridge.asComplex_spec _value_i12 (Litex.rationalToComplex _value_i12 h_22036)))) (by ring!))
                )
            )
          have h_22020 : (by
            let _equal_wd_2_0 := _object_w57
            let _equal_wd_2_1 := _object_w60
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  ((((((((h_22015).trans h_22016)).trans h_22019)).trans (h_22018).symm)).trans (h_22017).symm)
                )
            )
          exact (And.intro h_22013 (And.intro h_22014 (And.intro h_22015 (And.intro h_22016 (And.intro h_22017 (And.intro h_22018 (And.intro h_22019 h_22020)))))))
        );
        let h_28204 : (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact Litex.Subset _atomic_wd_1_0 (Litex.Q (M := M))) := (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact (by
            let _set := _atomic_wd_1_0
            exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Q (M := M)) _set.wd (by
            let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℚ) / (2 : ℚ)) (by norm_num)))) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Q (M := M)) _set.val.tail.wd (by
            let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℚ) / (3 : ℚ)) (by norm_num)))) (Litex.emptySubset (Litex.Q (M := M)))))));
        Litex.finiteFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True)) h_19022 (Litex.formulaFnInFnSet _wd_1_1) (Litex.formulaFnInFnSet _wd_1_2) h_19036 (fun i hi => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.rational) (Litex.denote (Litex.Q (M := M))) (M.standard_isSet Litex.StandardSetValue.rational) (Litex.isSet (Litex.Q (M := M))) (fun (_raw_i1 : M.Value) => True) i).mpr ⟨h_28204 i hi, True.intro⟩) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x1 _fold_h1 => (And.right (And.right (And.right (h_19041 _fold_x0 _fold_h0 _fold_x1 _fold_h1)))))))) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x2 _fold_h2 => (And.right (And.right (And.right (And.right (And.right (And.right (And.right (h_22021 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2))))))))))))))));
        let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((Eq.refl (Litex.denote (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        (let _setElement_0 := _wd_2_0;
          let _setElement_1 := _wd_2_1;
          let _setTail_2 := Litex.emptySet (M := M);
          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
            let _atomic_wd_1_0 := _wd_2_0
            let _atomic_wd_1_1 := _wd_2_1
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _atomic_wd_1_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_1).wd.1 (_atomic_wd_1_1).wd.2.1 (_atomic_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0));
        let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
          intro _raw_i1 h_27 _
          let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_27)
          have h_27 : Litex.In _value_i1 (Litex.Q (M := M)) := h_27
          change Litex.In _value_i1 (Litex.Q (M := M))
          exact h_27));
        let _wd_1_2 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
          intro _raw_i2 _raw_i3 h_46 h_47 _
          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_46)
          have h_46 : Litex.In _value_i2 (Litex.Q (M := M)) := h_46
          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_47)
          have h_47 : Litex.In _value_i3 (Litex.Q (M := M)) := h_47
          change (by
            let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_46) (Litex.rationalToComplex _value_i3 h_47))
            exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
          exact (by
            let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_46) (Litex.rationalToComplex _value_i3 h_47))
            exact (Litex.mulInQ _value_i2 _value_i3 h_46 h_47))));
        let _wd_1_3 := (Litex.number (M := M) (2 : ℂ));
        (let h_125 : (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact Litex.IsFiniteSet _atomic_wd_1_0) := (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact (let _finite_tail_0 := _atomic_wd_1_0;
          let _finite_tail_1 := _finite_tail_0.val.tail;
          let _finite_tail_2 := _finite_tail_1.val.tail;
          have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
          have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
          have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
          _finite_0));
        let h_139 : Litex.In _wd_1_3 (Litex.Q (M := M)) := (Litex.NativeBridge.numberInQOfEq (M := M) (2 : ℂ) (2 : ℚ) (by norm_num));
        let h_144 : ∀ {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_157 : Litex.In _value_i4 (Litex.Q (M := M))) {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_158 : Litex.In _value_i5 (Litex.Q (M := M))), (by
          let _object_w4 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_172 h_173 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_172)
            have h_172 : Litex.In _value_i2 (Litex.Q (M := M)) := h_172
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_173)
            have h_173 : Litex.In _value_i3 (Litex.Q (M := M)) := h_173
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_172) (Litex.rationalToComplex _value_i3 h_173))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_172) (Litex.rationalToComplex _value_i3 h_173))
              exact (Litex.mulInQ _value_i2 _value_i3 h_172 h_173))));
          let _wd_2_1 := _value_i4;
          let _wd_2_2 := _value_i5;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_157 h_158 True.intro))
          let _object_w5 := (Litex.mul _value_i4 _value_i5 (Litex.rationalToComplex _value_i4 h_157) (Litex.rationalToComplex _value_i5 h_158))
          let _object_w6 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_1648 h_1649 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1648)
            have h_1648 : Litex.In _value_i2 (Litex.Q (M := M)) := h_1648
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1649)
            have h_1649 : Litex.In _value_i3 (Litex.Q (M := M)) := h_1649
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_1648) (Litex.rationalToComplex _value_i3 h_1649))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_1648) (Litex.rationalToComplex _value_i3 h_1649))
              exact (Litex.mulInQ _value_i2 _value_i3 h_1648 h_1649))));
          let _wd_2_1 := _value_i5;
          let _wd_2_2 := _value_i4;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_158 h_157 True.intro))
          let _object_w7 := (Litex.mul _value_i5 _value_i4 (Litex.rationalToComplex _value_i5 h_158) (Litex.rationalToComplex _value_i4 h_157))
          exact (((by
            let _equal_wd_1_0 := _object_w4
            let _equal_wd_1_1 := _object_w5
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w6
            let _equal_wd_1_1 := _object_w7
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w5
            let _equal_wd_1_1 := _object_w7
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
            let _equal_wd_1_0 := _object_w4
            let _equal_wd_1_1 := _object_w6
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))
        ) := (by
          intro _Host_i4 _rep_i4 _value_i4 h_157 _Host_i5 _rep_i5 _value_i5 h_158
          let _object_w4 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_172 h_173 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_172)
            have h_172 : Litex.In _value_i2 (Litex.Q (M := M)) := h_172
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_173)
            have h_173 : Litex.In _value_i3 (Litex.Q (M := M)) := h_173
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_172) (Litex.rationalToComplex _value_i3 h_173))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_172) (Litex.rationalToComplex _value_i3 h_173))
              exact (Litex.mulInQ _value_i2 _value_i3 h_172 h_173))));
          let _wd_2_1 := _value_i4;
          let _wd_2_2 := _value_i5;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_157 h_158 True.intro))
          let _object_w5 := (Litex.mul _value_i4 _value_i5 (Litex.rationalToComplex _value_i4 h_157) (Litex.rationalToComplex _value_i5 h_158))
          have h_140 : (by
            let _equal_wd_1_0 := _object_w4
            let _equal_wd_1_1 := _object_w5
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])) = (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from by
                    have _litex_residual : (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) = (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])) = (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from by
                    let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_1299 h_1300 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1299)
                      have h_1299 : Litex.In _value_i2 (Litex.Q (M := M)) := h_1299
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1300)
                      have h_1300 : Litex.In _value_i3 (Litex.Q (M := M)) := h_1300
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_1299) (Litex.rationalToComplex _value_i3 h_1300))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_1299) (Litex.rationalToComplex _value_i3 h_1300))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_1299 h_1300))));
                    let _wd_2_1 := _value_i4;
                    let _wd_2_2 := _value_i5;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_157 h_158 True.intro))
                    let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_1442 h_1443 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1442)
                      have h_1442 : Litex.In _value_i2 (Litex.Q (M := M)) := h_1442
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1443)
                      have h_1443 : Litex.In _value_i3 (Litex.Q (M := M)) := h_1443
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_1442) (Litex.rationalToComplex _value_i3 h_1443))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_1442) (Litex.rationalToComplex _value_i3 h_1443))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_1442 h_1443))));
                    let _wd_2_1 := _value_i4;
                    let _wd_2_2 := _value_i5;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_157 h_158 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          let _object_w6 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_1648 h_1649 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1648)
            have h_1648 : Litex.In _value_i2 (Litex.Q (M := M)) := h_1648
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1649)
            have h_1649 : Litex.In _value_i3 (Litex.Q (M := M)) := h_1649
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_1648) (Litex.rationalToComplex _value_i3 h_1649))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_1648) (Litex.rationalToComplex _value_i3 h_1649))
              exact (Litex.mulInQ _value_i2 _value_i3 h_1648 h_1649))));
          let _wd_2_1 := _value_i5;
          let _wd_2_2 := _value_i4;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_158 h_157 True.intro))
          let _object_w7 := (Litex.mul _value_i5 _value_i4 (Litex.rationalToComplex _value_i5 h_158) (Litex.rationalToComplex _value_i4 h_157))
          have h_141 : (by
            let _equal_wd_1_0 := _object_w6
            let _equal_wd_1_1 := _object_w7
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i4)])) = (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i4)) from by
                    have _litex_residual : (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i4)) = (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i4)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i4)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i4)])) = (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i4)) from by
                    let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_2775 h_2776 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_2775)
                      have h_2775 : Litex.In _value_i2 (Litex.Q (M := M)) := h_2775
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_2776)
                      have h_2776 : Litex.In _value_i3 (Litex.Q (M := M)) := h_2776
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_2775) (Litex.rationalToComplex _value_i3 h_2776))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_2775) (Litex.rationalToComplex _value_i3 h_2776))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_2775 h_2776))));
                    let _wd_2_1 := _value_i5;
                    let _wd_2_2 := _value_i4;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_158 h_157 True.intro))
                    let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_2918 h_2919 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_2918)
                      have h_2918 : Litex.In _value_i2 (Litex.Q (M := M)) := h_2918
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_2919)
                      have h_2919 : Litex.In _value_i3 (Litex.Q (M := M)) := h_2919
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_2918) (Litex.rationalToComplex _value_i3 h_2919))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_2918) (Litex.rationalToComplex _value_i3 h_2919))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_2918 h_2919))));
                    let _wd_2_1 := _value_i5;
                    let _wd_2_2 := _value_i4;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_158 h_157 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i4)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          have h_142 : (by
            let _equal_wd_1_0 := _object_w5
            let _equal_wd_1_1 := _object_w7
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i4 (Litex.rationalToComplex _value_i4 h_157)) * (Litex.NativeBridge.asComplex _value_i5 (Litex.rationalToComplex _value_i5 h_158))) ((Litex.NativeBridge.asComplex _value_i5 (Litex.rationalToComplex _value_i5 h_158)) * (Litex.NativeBridge.asComplex _value_i4 (Litex.rationalToComplex _value_i4 h_157))) (Litex.NativeBridge.denoteMul _value_i4 _value_i5 (_object_w5).wd.1 (_object_w5).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.rationalToComplex _value_i4 h_157)) (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.rationalToComplex _value_i5 h_158))) (Litex.NativeBridge.denoteMul _value_i5 _value_i4 (_object_w7).wd.1 (_object_w7).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.rationalToComplex _value_i5 h_158)) (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.rationalToComplex _value_i4 h_157))) (by ring!))
                )
            )
          have h_143 : (by
            let _equal_wd_1_0 := _object_w4
            let _equal_wd_1_1 := _object_w6
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  ((((h_140).trans h_142)).trans (h_141).symm)
                )
            )
          exact (And.intro h_140 (And.intro h_141 (And.intro h_142 h_143)))
        );
        let h_3124 : ∀ {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_3137 : Litex.In _value_i4 (Litex.Q (M := M))) {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_3138 : Litex.In _value_i5 (Litex.Q (M := M))) {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_3139 : Litex.In _value_i6 (Litex.Q (M := M))), (by
          let _object_w9 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_3153 h_3154 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3153)
            have h_3153 : Litex.In _value_i2 (Litex.Q (M := M)) := h_3153
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_3154)
            have h_3154 : Litex.In _value_i3 (Litex.Q (M := M)) := h_3154
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_3153) (Litex.rationalToComplex _value_i3 h_3154))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_3153) (Litex.rationalToComplex _value_i3 h_3154))
              exact (Litex.mulInQ _value_i2 _value_i3 h_3153 h_3154))));
          let _wd_2_1 := _value_i4;
          let _wd_2_2 := _value_i5;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3137 h_3138 True.intro))
          let _object_w10 := (Litex.mul _value_i4 _value_i5 (Litex.rationalToComplex _value_i4 h_3137) (Litex.rationalToComplex _value_i5 h_3138))
          let _object_w11 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_4881 h_4882 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4881)
            have h_4881 : Litex.In _value_i2 (Litex.Q (M := M)) := h_4881
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_4882)
            have h_4882 : Litex.In _value_i3 (Litex.Q (M := M)) := h_4882
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_4881) (Litex.rationalToComplex _value_i3 h_4882))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_4881) (Litex.rationalToComplex _value_i3 h_4882))
              exact (Litex.mulInQ _value_i2 _value_i3 h_4881 h_4882))));
          let _wd_2_1 := _value_i5;
          let _wd_2_2 := _value_i6;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3138 h_3139 True.intro))
          let _object_w12 := (Litex.mul _value_i5 _value_i6 (Litex.rationalToComplex _value_i5 h_3138) (Litex.rationalToComplex _value_i6 h_3139))
          let _object_w13 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_6645 h_6646 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6645)
            have h_6645 : Litex.In _value_i2 (Litex.Q (M := M)) := h_6645
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6646)
            have h_6646 : Litex.In _value_i3 (Litex.Q (M := M)) := h_6646
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6645) (Litex.rationalToComplex _value_i3 h_6646))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6645) (Litex.rationalToComplex _value_i3 h_6646))
              exact (Litex.mulInQ _value_i2 _value_i3 h_6645 h_6646))));
          let _wd_2_1 := _object_w9;
          let _wd_2_2 := _value_i6;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
            let _atomic_wd_1_0 := _object_w9
            exact (Litex.inOfSame _object_w9 _object_w9 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w9) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w9))) h_3139 True.intro))
          let _object_w14 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_6859 h_6860 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6859)
            have h_6859 : Litex.In _value_i2 (Litex.Q (M := M)) := h_6859
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6860)
            have h_6860 : Litex.In _value_i3 (Litex.Q (M := M)) := h_6860
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6859) (Litex.rationalToComplex _value_i3 h_6860))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6859) (Litex.rationalToComplex _value_i3 h_6860))
              exact (Litex.mulInQ _value_i2 _value_i3 h_6859 h_6860))));
          let _wd_2_1 := _object_w10;
          let _wd_2_2 := _value_i6;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
            let _atomic_wd_1_0 := _object_w10
            exact (Litex.mulInQ _value_i4 _value_i5 h_3137 h_3138)) h_3139 True.intro))
          let _object_w15 := (let _wd_2_0 := _object_w10;
          let _wd_2_1 := _value_i6;
          (Litex.mul _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _object_w10
            exact (Litex.mulInC _value_i4 _value_i5 (Litex.rationalToComplex _value_i4 h_3137) (Litex.rationalToComplex _value_i5 h_3138))) (Litex.rationalToComplex _wd_2_1 h_3139)))
          let _object_w16 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_7983 h_7984 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_7983)
            have h_7983 : Litex.In _value_i2 (Litex.Q (M := M)) := h_7983
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_7984)
            have h_7984 : Litex.In _value_i3 (Litex.Q (M := M)) := h_7984
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_7983) (Litex.rationalToComplex _value_i3 h_7984))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_7983) (Litex.rationalToComplex _value_i3 h_7984))
              exact (Litex.mulInQ _value_i2 _value_i3 h_7983 h_7984))));
          let _wd_2_1 := _value_i4;
          let _wd_2_2 := _object_w11;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3137 (by
            let _atomic_wd_1_0 := _object_w11
            exact (Litex.inOfSame _object_w11 _object_w11 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w11) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w11))) True.intro))
          let _object_w17 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_8193 h_8194 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_8193)
            have h_8193 : Litex.In _value_i2 (Litex.Q (M := M)) := h_8193
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_8194)
            have h_8194 : Litex.In _value_i3 (Litex.Q (M := M)) := h_8194
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_8193) (Litex.rationalToComplex _value_i3 h_8194))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_8193) (Litex.rationalToComplex _value_i3 h_8194))
              exact (Litex.mulInQ _value_i2 _value_i3 h_8193 h_8194))));
          let _wd_2_1 := _value_i4;
          let _wd_2_2 := _object_w12;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3137 (by
            let _atomic_wd_1_0 := _object_w12
            exact (Litex.mulInQ _value_i5 _value_i6 h_3138 h_3139)) True.intro))
          let _object_w18 := (let _wd_2_0 := _value_i4;
          let _wd_2_1 := _object_w12;
          (Litex.mul _wd_2_0 _wd_2_1 (Litex.rationalToComplex _wd_2_0 h_3137) (by
            let _atomic_wd_1_0 := _object_w12
            exact (Litex.mulInC _value_i5 _value_i6 (Litex.rationalToComplex _value_i5 h_3138) (Litex.rationalToComplex _value_i6 h_3139)))))
          exact (((by
            let _equal_wd_1_0 := _object_w9
            let _equal_wd_1_1 := _object_w10
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w11
            let _equal_wd_1_1 := _object_w12
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w13
            let _equal_wd_1_1 := _object_w14
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w14
            let _equal_wd_1_1 := _object_w15
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w16
            let _equal_wd_1_1 := _object_w17
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w17
            let _equal_wd_1_1 := _object_w18
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w15
            let _equal_wd_1_1 := _object_w18
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
            let _equal_wd_1_0 := _object_w13
            let _equal_wd_1_1 := _object_w16
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))))))))))
        ) := (by
          intro _Host_i4 _rep_i4 _value_i4 h_3137 _Host_i5 _rep_i5 _value_i5 h_3138 _Host_i6 _rep_i6 _value_i6 h_3139
          let _object_w9 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_3153 h_3154 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3153)
            have h_3153 : Litex.In _value_i2 (Litex.Q (M := M)) := h_3153
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_3154)
            have h_3154 : Litex.In _value_i3 (Litex.Q (M := M)) := h_3154
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_3153) (Litex.rationalToComplex _value_i3 h_3154))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_3153) (Litex.rationalToComplex _value_i3 h_3154))
              exact (Litex.mulInQ _value_i2 _value_i3 h_3153 h_3154))));
          let _wd_2_1 := _value_i4;
          let _wd_2_2 := _value_i5;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3137 h_3138 True.intro))
          let _object_w10 := (Litex.mul _value_i4 _value_i5 (Litex.rationalToComplex _value_i4 h_3137) (Litex.rationalToComplex _value_i5 h_3138))
          have h_3116 : (by
            let _equal_wd_1_0 := _object_w9
            let _equal_wd_1_1 := _object_w10
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])) = (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from by
                    have _litex_residual : (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) = (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])) = (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from by
                    let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_4476 h_4477 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4476)
                      have h_4476 : Litex.In _value_i2 (Litex.Q (M := M)) := h_4476
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_4477)
                      have h_4477 : Litex.In _value_i3 (Litex.Q (M := M)) := h_4477
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_4476) (Litex.rationalToComplex _value_i3 h_4477))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_4476) (Litex.rationalToComplex _value_i3 h_4477))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_4476 h_4477))));
                    let _wd_2_1 := _value_i4;
                    let _wd_2_2 := _value_i5;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3137 h_3138 True.intro))
                    let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_4639 h_4640 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4639)
                      have h_4639 : Litex.In _value_i2 (Litex.Q (M := M)) := h_4639
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_4640)
                      have h_4640 : Litex.In _value_i3 (Litex.Q (M := M)) := h_4640
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_4639) (Litex.rationalToComplex _value_i3 h_4640))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_4639) (Litex.rationalToComplex _value_i3 h_4640))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_4639 h_4640))));
                    let _wd_2_1 := _value_i4;
                    let _wd_2_2 := _value_i5;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3137 h_3138 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          let _object_w11 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_4881 h_4882 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4881)
            have h_4881 : Litex.In _value_i2 (Litex.Q (M := M)) := h_4881
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_4882)
            have h_4882 : Litex.In _value_i3 (Litex.Q (M := M)) := h_4882
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_4881) (Litex.rationalToComplex _value_i3 h_4882))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_4881) (Litex.rationalToComplex _value_i3 h_4882))
              exact (Litex.mulInQ _value_i2 _value_i3 h_4881 h_4882))));
          let _wd_2_1 := _value_i5;
          let _wd_2_2 := _value_i6;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3138 h_3139 True.intro))
          let _object_w12 := (Litex.mul _value_i5 _value_i6 (Litex.rationalToComplex _value_i5 h_3138) (Litex.rationalToComplex _value_i6 h_3139))
          have h_3117 : (by
            let _equal_wd_1_0 := _object_w11
            let _equal_wd_1_1 := _object_w12
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i6)])) = (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6)) from by
                    have _litex_residual : (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6)) = (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i6)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i6)])) = (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6)) from by
                    let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_6232 h_6233 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6232)
                      have h_6232 : Litex.In _value_i2 (Litex.Q (M := M)) := h_6232
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6233)
                      have h_6233 : Litex.In _value_i3 (Litex.Q (M := M)) := h_6233
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6232) (Litex.rationalToComplex _value_i3 h_6233))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6232) (Litex.rationalToComplex _value_i3 h_6233))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_6232 h_6233))));
                    let _wd_2_1 := _value_i5;
                    let _wd_2_2 := _value_i6;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3138 h_3139 True.intro))
                    let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_6399 h_6400 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6399)
                      have h_6399 : Litex.In _value_i2 (Litex.Q (M := M)) := h_6399
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6400)
                      have h_6400 : Litex.In _value_i3 (Litex.Q (M := M)) := h_6400
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6399) (Litex.rationalToComplex _value_i3 h_6400))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6399) (Litex.rationalToComplex _value_i3 h_6400))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_6399 h_6400))));
                    let _wd_2_1 := _value_i5;
                    let _wd_2_2 := _value_i6;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3138 h_3139 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          let _object_w13 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_6645 h_6646 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6645)
            have h_6645 : Litex.In _value_i2 (Litex.Q (M := M)) := h_6645
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6646)
            have h_6646 : Litex.In _value_i3 (Litex.Q (M := M)) := h_6646
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6645) (Litex.rationalToComplex _value_i3 h_6646))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6645) (Litex.rationalToComplex _value_i3 h_6646))
              exact (Litex.mulInQ _value_i2 _value_i3 h_6645 h_6646))));
          let _wd_2_1 := _object_w9;
          let _wd_2_2 := _value_i6;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
            let _atomic_wd_1_0 := _object_w9
            exact (Litex.inOfSame _object_w9 _object_w9 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w9) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w9))) h_3139 True.intro))
          let _object_w14 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_6859 h_6860 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6859)
            have h_6859 : Litex.In _value_i2 (Litex.Q (M := M)) := h_6859
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6860)
            have h_6860 : Litex.In _value_i3 (Litex.Q (M := M)) := h_6860
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6859) (Litex.rationalToComplex _value_i3 h_6860))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6859) (Litex.rationalToComplex _value_i3 h_6860))
              exact (Litex.mulInQ _value_i2 _value_i3 h_6859 h_6860))));
          let _wd_2_1 := _object_w10;
          let _wd_2_2 := _value_i6;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
            let _atomic_wd_1_0 := _object_w10
            exact (Litex.mulInQ _value_i4 _value_i5 h_3137 h_3138)) h_3139 True.intro))
          have h_3118 : (by
            let _equal_wd_1_0 := _object_w13
            let _equal_wd_1_1 := _object_w14
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) h_3116 (show @Eq M.Value _ _ from Eq.refl _)))
                )
            )
          let _object_w15 := (let _wd_2_0 := _object_w10;
          let _wd_2_1 := _value_i6;
          (Litex.mul _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _object_w10
            exact (Litex.mulInC _value_i4 _value_i5 (Litex.rationalToComplex _value_i4 h_3137) (Litex.rationalToComplex _value_i5 h_3138))) (Litex.rationalToComplex _wd_2_1 h_3139)))
          have h_3119 : (by
            let _equal_wd_1_0 := _object_w14
            let _equal_wd_1_1 := _object_w15
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)), (Litex.denote _value_i6)])) = (M.mulValue (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (Litex.denote _value_i6)) from by
                    have _litex_residual : (M.mulValue (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (Litex.denote _value_i6)) = (M.mulValue (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (Litex.denote _value_i6)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)), (Litex.denote _value_i6)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)), (Litex.denote _value_i6)])) = (M.mulValue (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (Litex.denote _value_i6)) from by
                    let _litex_original := _object_w14
                    let _litex_literal := _object_w14
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (Litex.denote _value_i6)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          let _object_w16 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_7983 h_7984 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_7983)
            have h_7983 : Litex.In _value_i2 (Litex.Q (M := M)) := h_7983
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_7984)
            have h_7984 : Litex.In _value_i3 (Litex.Q (M := M)) := h_7984
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_7983) (Litex.rationalToComplex _value_i3 h_7984))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_7983) (Litex.rationalToComplex _value_i3 h_7984))
              exact (Litex.mulInQ _value_i2 _value_i3 h_7983 h_7984))));
          let _wd_2_1 := _value_i4;
          let _wd_2_2 := _object_w11;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3137 (by
            let _atomic_wd_1_0 := _object_w11
            exact (Litex.inOfSame _object_w11 _object_w11 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w11) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w11))) True.intro))
          let _object_w17 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_8193 h_8194 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_8193)
            have h_8193 : Litex.In _value_i2 (Litex.Q (M := M)) := h_8193
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_8194)
            have h_8194 : Litex.In _value_i3 (Litex.Q (M := M)) := h_8194
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_8193) (Litex.rationalToComplex _value_i3 h_8194))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_8193) (Litex.rationalToComplex _value_i3 h_8194))
              exact (Litex.mulInQ _value_i2 _value_i3 h_8193 h_8194))));
          let _wd_2_1 := _value_i4;
          let _wd_2_2 := _object_w12;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3137 (by
            let _atomic_wd_1_0 := _object_w12
            exact (Litex.mulInQ _value_i5 _value_i6 h_3138 h_3139)) True.intro))
          have h_3120 : (by
            let _equal_wd_1_0 := _object_w16
            let _equal_wd_1_1 := _object_w17
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_3117))
                )
            )
          let _object_w18 := (let _wd_2_0 := _value_i4;
          let _wd_2_1 := _object_w12;
          (Litex.mul _wd_2_0 _wd_2_1 (Litex.rationalToComplex _wd_2_0 h_3137) (by
            let _atomic_wd_1_0 := _object_w12
            exact (Litex.mulInC _value_i5 _value_i6 (Litex.rationalToComplex _value_i5 h_3138) (Litex.rationalToComplex _value_i6 h_3139)))))
          have h_3121 : (by
            let _equal_wd_1_0 := _object_w17
            let _equal_wd_1_1 := _object_w18
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6))])) = (M.mulValue (Litex.denote _value_i4) (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6))) from by
                    have _litex_residual : (M.mulValue (Litex.denote _value_i4) (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6))) = (M.mulValue (Litex.denote _value_i4) (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6))])) = (M.mulValue (Litex.denote _value_i4) (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6))) from by
                    let _litex_original := _object_w17
                    let _litex_literal := _object_w17
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i4) (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6))) from rfl))
                  ))).trans _litex_residual)
                )
            )
          have h_3122 : (by
            let _equal_wd_1_0 := _object_w15
            let _equal_wd_1_1 := _object_w18
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i4 (Litex.rationalToComplex _value_i4 h_3137)) * (Litex.NativeBridge.asComplex _value_i5 (Litex.rationalToComplex _value_i5 h_3138))) * (Litex.NativeBridge.asComplex _value_i6 (Litex.rationalToComplex _value_i6 h_3139))) ((Litex.NativeBridge.asComplex _value_i4 (Litex.rationalToComplex _value_i4 h_3137)) * ((Litex.NativeBridge.asComplex _value_i5 (Litex.rationalToComplex _value_i5 h_3138)) * (Litex.NativeBridge.asComplex _value_i6 (Litex.rationalToComplex _value_i6 h_3139)))) (Litex.NativeBridge.denoteMul (_object_w15).val.left _value_i6 (_object_w15).wd.1 (_object_w15).wd.2 _ _ (Litex.NativeBridge.denoteMul _value_i4 _value_i5 (_object_w10).wd.1 (_object_w10).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.rationalToComplex _value_i4 h_3137)) (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.rationalToComplex _value_i5 h_3138))) (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.rationalToComplex _value_i6 h_3139))) (Litex.NativeBridge.denoteMul _value_i4 (_object_w18).val.right (_object_w18).wd.1 (_object_w18).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.rationalToComplex _value_i4 h_3137)) (Litex.NativeBridge.denoteMul _value_i5 _value_i6 (_object_w12).wd.1 (_object_w12).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.rationalToComplex _value_i5 h_3138)) (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.rationalToComplex _value_i6 h_3139)))) (by ring!))
                )
            )
          have h_3123 : (by
            let _equal_wd_1_0 := _object_w13
            let _equal_wd_1_1 := _object_w16
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  ((((((((h_3118).trans h_3119)).trans h_3122)).trans (h_3121).symm)).trans (h_3120).symm)
                )
            )
          exact (And.intro h_3116 (And.intro h_3117 (And.intro h_3118 (And.intro h_3119 (And.intro h_3120 (And.intro h_3121 (And.intro h_3122 h_3123)))))))
        );
        let h_9307 : (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact Litex.Subset _atomic_wd_1_0 (Litex.Q (M := M))) := (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact (by
            let _set := _atomic_wd_1_0
            exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Q (M := M)) _set.wd (by
            let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℚ) / (2 : ℚ)) (by norm_num)))) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Q (M := M)) _set.val.tail.wd (by
            let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℚ) / (3 : ℚ)) (by norm_num)))) (Litex.emptySubset (Litex.Q (M := M)))))));
        Litex.finiteFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True)) h_125 (Litex.formulaFnInFnSet _wd_1_1) (Litex.formulaFnInFnSet _wd_1_2) h_139 (fun i hi => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.rational) (Litex.denote (Litex.Q (M := M))) (M.standard_isSet Litex.StandardSetValue.rational) (Litex.isSet (Litex.Q (M := M))) (fun (_raw_i1 : M.Value) => True) i).mpr ⟨h_9307 i hi, True.intro⟩) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x1 _fold_h1 => (And.right (And.right (And.right (h_144 _fold_x0 _fold_h0 _fold_x1 _fold_h1)))))))) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x2 _fold_h2 => (And.right (And.right (And.right (And.right (And.right (And.right (And.right (h_3124 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2))))))))))))))))))).trans (show (Litex.denote (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        (let _setElement_0 := _wd_2_0;
          let _setElement_1 := _wd_2_1;
          let _setTail_2 := Litex.emptySet (M := M);
          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
            let _atomic_wd_1_0 := _wd_2_0
            let _atomic_wd_1_1 := _wd_2_1
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _atomic_wd_1_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_1).wd.1 (_atomic_wd_1_1).wd.2.1 (_atomic_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0));
        let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
          intro _raw_i1 h_27 _
          let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_27)
          have h_27 : Litex.In _value_i1 (Litex.Q (M := M)) := h_27
          change Litex.In _value_i1 (Litex.Q (M := M))
          exact h_27));
        let _wd_1_2 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
          intro _raw_i2 _raw_i3 h_46 h_47 _
          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_46)
          have h_46 : Litex.In _value_i2 (Litex.Q (M := M)) := h_46
          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_47)
          have h_47 : Litex.In _value_i3 (Litex.Q (M := M)) := h_47
          change (by
            let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_46) (Litex.rationalToComplex _value_i3 h_47))
            exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
          exact (by
            let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_46) (Litex.rationalToComplex _value_i3 h_47))
            exact (Litex.mulInQ _value_i2 _value_i3 h_46 h_47))));
        let _wd_1_3 := (Litex.number (M := M) (2 : ℂ));
        (let h_125 : (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact Litex.IsFiniteSet _atomic_wd_1_0) := (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact (let _finite_tail_0 := _atomic_wd_1_0;
          let _finite_tail_1 := _finite_tail_0.val.tail;
          let _finite_tail_2 := _finite_tail_1.val.tail;
          have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
          have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
          have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
          _finite_0));
        let h_139 : Litex.In _wd_1_3 (Litex.Q (M := M)) := (Litex.NativeBridge.numberInQOfEq (M := M) (2 : ℂ) (2 : ℚ) (by norm_num));
        let h_144 : ∀ {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_157 : Litex.In _value_i4 (Litex.Q (M := M))) {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_158 : Litex.In _value_i5 (Litex.Q (M := M))), (by
          let _object_w4 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_172 h_173 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_172)
            have h_172 : Litex.In _value_i2 (Litex.Q (M := M)) := h_172
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_173)
            have h_173 : Litex.In _value_i3 (Litex.Q (M := M)) := h_173
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_172) (Litex.rationalToComplex _value_i3 h_173))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_172) (Litex.rationalToComplex _value_i3 h_173))
              exact (Litex.mulInQ _value_i2 _value_i3 h_172 h_173))));
          let _wd_2_1 := _value_i4;
          let _wd_2_2 := _value_i5;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_157 h_158 True.intro))
          let _object_w5 := (Litex.mul _value_i4 _value_i5 (Litex.rationalToComplex _value_i4 h_157) (Litex.rationalToComplex _value_i5 h_158))
          let _object_w6 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_1648 h_1649 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1648)
            have h_1648 : Litex.In _value_i2 (Litex.Q (M := M)) := h_1648
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1649)
            have h_1649 : Litex.In _value_i3 (Litex.Q (M := M)) := h_1649
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_1648) (Litex.rationalToComplex _value_i3 h_1649))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_1648) (Litex.rationalToComplex _value_i3 h_1649))
              exact (Litex.mulInQ _value_i2 _value_i3 h_1648 h_1649))));
          let _wd_2_1 := _value_i5;
          let _wd_2_2 := _value_i4;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_158 h_157 True.intro))
          let _object_w7 := (Litex.mul _value_i5 _value_i4 (Litex.rationalToComplex _value_i5 h_158) (Litex.rationalToComplex _value_i4 h_157))
          exact (((by
            let _equal_wd_1_0 := _object_w4
            let _equal_wd_1_1 := _object_w5
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w6
            let _equal_wd_1_1 := _object_w7
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w5
            let _equal_wd_1_1 := _object_w7
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
            let _equal_wd_1_0 := _object_w4
            let _equal_wd_1_1 := _object_w6
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))
        ) := (by
          intro _Host_i4 _rep_i4 _value_i4 h_157 _Host_i5 _rep_i5 _value_i5 h_158
          let _object_w4 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_172 h_173 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_172)
            have h_172 : Litex.In _value_i2 (Litex.Q (M := M)) := h_172
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_173)
            have h_173 : Litex.In _value_i3 (Litex.Q (M := M)) := h_173
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_172) (Litex.rationalToComplex _value_i3 h_173))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_172) (Litex.rationalToComplex _value_i3 h_173))
              exact (Litex.mulInQ _value_i2 _value_i3 h_172 h_173))));
          let _wd_2_1 := _value_i4;
          let _wd_2_2 := _value_i5;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_157 h_158 True.intro))
          let _object_w5 := (Litex.mul _value_i4 _value_i5 (Litex.rationalToComplex _value_i4 h_157) (Litex.rationalToComplex _value_i5 h_158))
          have h_140 : (by
            let _equal_wd_1_0 := _object_w4
            let _equal_wd_1_1 := _object_w5
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])) = (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from by
                    have _litex_residual : (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) = (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])) = (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from by
                    let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_1299 h_1300 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1299)
                      have h_1299 : Litex.In _value_i2 (Litex.Q (M := M)) := h_1299
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1300)
                      have h_1300 : Litex.In _value_i3 (Litex.Q (M := M)) := h_1300
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_1299) (Litex.rationalToComplex _value_i3 h_1300))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_1299) (Litex.rationalToComplex _value_i3 h_1300))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_1299 h_1300))));
                    let _wd_2_1 := _value_i4;
                    let _wd_2_2 := _value_i5;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_157 h_158 True.intro))
                    let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_1442 h_1443 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1442)
                      have h_1442 : Litex.In _value_i2 (Litex.Q (M := M)) := h_1442
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1443)
                      have h_1443 : Litex.In _value_i3 (Litex.Q (M := M)) := h_1443
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_1442) (Litex.rationalToComplex _value_i3 h_1443))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_1442) (Litex.rationalToComplex _value_i3 h_1443))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_1442 h_1443))));
                    let _wd_2_1 := _value_i4;
                    let _wd_2_2 := _value_i5;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_157 h_158 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          let _object_w6 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_1648 h_1649 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1648)
            have h_1648 : Litex.In _value_i2 (Litex.Q (M := M)) := h_1648
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1649)
            have h_1649 : Litex.In _value_i3 (Litex.Q (M := M)) := h_1649
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_1648) (Litex.rationalToComplex _value_i3 h_1649))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_1648) (Litex.rationalToComplex _value_i3 h_1649))
              exact (Litex.mulInQ _value_i2 _value_i3 h_1648 h_1649))));
          let _wd_2_1 := _value_i5;
          let _wd_2_2 := _value_i4;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_158 h_157 True.intro))
          let _object_w7 := (Litex.mul _value_i5 _value_i4 (Litex.rationalToComplex _value_i5 h_158) (Litex.rationalToComplex _value_i4 h_157))
          have h_141 : (by
            let _equal_wd_1_0 := _object_w6
            let _equal_wd_1_1 := _object_w7
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i4)])) = (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i4)) from by
                    have _litex_residual : (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i4)) = (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i4)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i4)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i4)])) = (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i4)) from by
                    let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_2775 h_2776 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_2775)
                      have h_2775 : Litex.In _value_i2 (Litex.Q (M := M)) := h_2775
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_2776)
                      have h_2776 : Litex.In _value_i3 (Litex.Q (M := M)) := h_2776
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_2775) (Litex.rationalToComplex _value_i3 h_2776))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_2775) (Litex.rationalToComplex _value_i3 h_2776))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_2775 h_2776))));
                    let _wd_2_1 := _value_i5;
                    let _wd_2_2 := _value_i4;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_158 h_157 True.intro))
                    let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_2918 h_2919 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_2918)
                      have h_2918 : Litex.In _value_i2 (Litex.Q (M := M)) := h_2918
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_2919)
                      have h_2919 : Litex.In _value_i3 (Litex.Q (M := M)) := h_2919
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_2918) (Litex.rationalToComplex _value_i3 h_2919))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_2918) (Litex.rationalToComplex _value_i3 h_2919))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_2918 h_2919))));
                    let _wd_2_1 := _value_i5;
                    let _wd_2_2 := _value_i4;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_158 h_157 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i4)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          have h_142 : (by
            let _equal_wd_1_0 := _object_w5
            let _equal_wd_1_1 := _object_w7
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i4 (Litex.rationalToComplex _value_i4 h_157)) * (Litex.NativeBridge.asComplex _value_i5 (Litex.rationalToComplex _value_i5 h_158))) ((Litex.NativeBridge.asComplex _value_i5 (Litex.rationalToComplex _value_i5 h_158)) * (Litex.NativeBridge.asComplex _value_i4 (Litex.rationalToComplex _value_i4 h_157))) (Litex.NativeBridge.denoteMul _value_i4 _value_i5 (_object_w5).wd.1 (_object_w5).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.rationalToComplex _value_i4 h_157)) (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.rationalToComplex _value_i5 h_158))) (Litex.NativeBridge.denoteMul _value_i5 _value_i4 (_object_w7).wd.1 (_object_w7).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.rationalToComplex _value_i5 h_158)) (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.rationalToComplex _value_i4 h_157))) (by ring!))
                )
            )
          have h_143 : (by
            let _equal_wd_1_0 := _object_w4
            let _equal_wd_1_1 := _object_w6
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  ((((h_140).trans h_142)).trans (h_141).symm)
                )
            )
          exact (And.intro h_140 (And.intro h_141 (And.intro h_142 h_143)))
        );
        let h_3124 : ∀ {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_3137 : Litex.In _value_i4 (Litex.Q (M := M))) {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_3138 : Litex.In _value_i5 (Litex.Q (M := M))) {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_3139 : Litex.In _value_i6 (Litex.Q (M := M))), (by
          let _object_w9 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_3153 h_3154 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3153)
            have h_3153 : Litex.In _value_i2 (Litex.Q (M := M)) := h_3153
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_3154)
            have h_3154 : Litex.In _value_i3 (Litex.Q (M := M)) := h_3154
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_3153) (Litex.rationalToComplex _value_i3 h_3154))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_3153) (Litex.rationalToComplex _value_i3 h_3154))
              exact (Litex.mulInQ _value_i2 _value_i3 h_3153 h_3154))));
          let _wd_2_1 := _value_i4;
          let _wd_2_2 := _value_i5;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3137 h_3138 True.intro))
          let _object_w10 := (Litex.mul _value_i4 _value_i5 (Litex.rationalToComplex _value_i4 h_3137) (Litex.rationalToComplex _value_i5 h_3138))
          let _object_w11 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_4881 h_4882 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4881)
            have h_4881 : Litex.In _value_i2 (Litex.Q (M := M)) := h_4881
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_4882)
            have h_4882 : Litex.In _value_i3 (Litex.Q (M := M)) := h_4882
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_4881) (Litex.rationalToComplex _value_i3 h_4882))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_4881) (Litex.rationalToComplex _value_i3 h_4882))
              exact (Litex.mulInQ _value_i2 _value_i3 h_4881 h_4882))));
          let _wd_2_1 := _value_i5;
          let _wd_2_2 := _value_i6;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3138 h_3139 True.intro))
          let _object_w12 := (Litex.mul _value_i5 _value_i6 (Litex.rationalToComplex _value_i5 h_3138) (Litex.rationalToComplex _value_i6 h_3139))
          let _object_w13 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_6645 h_6646 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6645)
            have h_6645 : Litex.In _value_i2 (Litex.Q (M := M)) := h_6645
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6646)
            have h_6646 : Litex.In _value_i3 (Litex.Q (M := M)) := h_6646
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6645) (Litex.rationalToComplex _value_i3 h_6646))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6645) (Litex.rationalToComplex _value_i3 h_6646))
              exact (Litex.mulInQ _value_i2 _value_i3 h_6645 h_6646))));
          let _wd_2_1 := _object_w9;
          let _wd_2_2 := _value_i6;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
            let _atomic_wd_1_0 := _object_w9
            exact (Litex.inOfSame _object_w9 _object_w9 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w9) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w9))) h_3139 True.intro))
          let _object_w14 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_6859 h_6860 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6859)
            have h_6859 : Litex.In _value_i2 (Litex.Q (M := M)) := h_6859
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6860)
            have h_6860 : Litex.In _value_i3 (Litex.Q (M := M)) := h_6860
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6859) (Litex.rationalToComplex _value_i3 h_6860))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6859) (Litex.rationalToComplex _value_i3 h_6860))
              exact (Litex.mulInQ _value_i2 _value_i3 h_6859 h_6860))));
          let _wd_2_1 := _object_w10;
          let _wd_2_2 := _value_i6;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
            let _atomic_wd_1_0 := _object_w10
            exact (Litex.mulInQ _value_i4 _value_i5 h_3137 h_3138)) h_3139 True.intro))
          let _object_w15 := (let _wd_2_0 := _object_w10;
          let _wd_2_1 := _value_i6;
          (Litex.mul _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _object_w10
            exact (Litex.mulInC _value_i4 _value_i5 (Litex.rationalToComplex _value_i4 h_3137) (Litex.rationalToComplex _value_i5 h_3138))) (Litex.rationalToComplex _wd_2_1 h_3139)))
          let _object_w16 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_7983 h_7984 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_7983)
            have h_7983 : Litex.In _value_i2 (Litex.Q (M := M)) := h_7983
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_7984)
            have h_7984 : Litex.In _value_i3 (Litex.Q (M := M)) := h_7984
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_7983) (Litex.rationalToComplex _value_i3 h_7984))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_7983) (Litex.rationalToComplex _value_i3 h_7984))
              exact (Litex.mulInQ _value_i2 _value_i3 h_7983 h_7984))));
          let _wd_2_1 := _value_i4;
          let _wd_2_2 := _object_w11;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3137 (by
            let _atomic_wd_1_0 := _object_w11
            exact (Litex.inOfSame _object_w11 _object_w11 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w11) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w11))) True.intro))
          let _object_w17 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_8193 h_8194 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_8193)
            have h_8193 : Litex.In _value_i2 (Litex.Q (M := M)) := h_8193
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_8194)
            have h_8194 : Litex.In _value_i3 (Litex.Q (M := M)) := h_8194
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_8193) (Litex.rationalToComplex _value_i3 h_8194))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_8193) (Litex.rationalToComplex _value_i3 h_8194))
              exact (Litex.mulInQ _value_i2 _value_i3 h_8193 h_8194))));
          let _wd_2_1 := _value_i4;
          let _wd_2_2 := _object_w12;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3137 (by
            let _atomic_wd_1_0 := _object_w12
            exact (Litex.mulInQ _value_i5 _value_i6 h_3138 h_3139)) True.intro))
          let _object_w18 := (let _wd_2_0 := _value_i4;
          let _wd_2_1 := _object_w12;
          (Litex.mul _wd_2_0 _wd_2_1 (Litex.rationalToComplex _wd_2_0 h_3137) (by
            let _atomic_wd_1_0 := _object_w12
            exact (Litex.mulInC _value_i5 _value_i6 (Litex.rationalToComplex _value_i5 h_3138) (Litex.rationalToComplex _value_i6 h_3139)))))
          exact (((by
            let _equal_wd_1_0 := _object_w9
            let _equal_wd_1_1 := _object_w10
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w11
            let _equal_wd_1_1 := _object_w12
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w13
            let _equal_wd_1_1 := _object_w14
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w14
            let _equal_wd_1_1 := _object_w15
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w16
            let _equal_wd_1_1 := _object_w17
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w17
            let _equal_wd_1_1 := _object_w18
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
            let _equal_wd_1_0 := _object_w15
            let _equal_wd_1_1 := _object_w18
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
            let _equal_wd_1_0 := _object_w13
            let _equal_wd_1_1 := _object_w16
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))))))))))
        ) := (by
          intro _Host_i4 _rep_i4 _value_i4 h_3137 _Host_i5 _rep_i5 _value_i5 h_3138 _Host_i6 _rep_i6 _value_i6 h_3139
          let _object_w9 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_3153 h_3154 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3153)
            have h_3153 : Litex.In _value_i2 (Litex.Q (M := M)) := h_3153
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_3154)
            have h_3154 : Litex.In _value_i3 (Litex.Q (M := M)) := h_3154
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_3153) (Litex.rationalToComplex _value_i3 h_3154))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_3153) (Litex.rationalToComplex _value_i3 h_3154))
              exact (Litex.mulInQ _value_i2 _value_i3 h_3153 h_3154))));
          let _wd_2_1 := _value_i4;
          let _wd_2_2 := _value_i5;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3137 h_3138 True.intro))
          let _object_w10 := (Litex.mul _value_i4 _value_i5 (Litex.rationalToComplex _value_i4 h_3137) (Litex.rationalToComplex _value_i5 h_3138))
          have h_3116 : (by
            let _equal_wd_1_0 := _object_w9
            let _equal_wd_1_1 := _object_w10
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])) = (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from by
                    have _litex_residual : (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) = (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])) = (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from by
                    let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_4476 h_4477 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4476)
                      have h_4476 : Litex.In _value_i2 (Litex.Q (M := M)) := h_4476
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_4477)
                      have h_4477 : Litex.In _value_i3 (Litex.Q (M := M)) := h_4477
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_4476) (Litex.rationalToComplex _value_i3 h_4477))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_4476) (Litex.rationalToComplex _value_i3 h_4477))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_4476 h_4477))));
                    let _wd_2_1 := _value_i4;
                    let _wd_2_2 := _value_i5;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3137 h_3138 True.intro))
                    let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_4639 h_4640 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4639)
                      have h_4639 : Litex.In _value_i2 (Litex.Q (M := M)) := h_4639
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_4640)
                      have h_4640 : Litex.In _value_i3 (Litex.Q (M := M)) := h_4640
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_4639) (Litex.rationalToComplex _value_i3 h_4640))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_4639) (Litex.rationalToComplex _value_i3 h_4640))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_4639 h_4640))));
                    let _wd_2_1 := _value_i4;
                    let _wd_2_2 := _value_i5;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3137 h_3138 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          let _object_w11 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_4881 h_4882 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4881)
            have h_4881 : Litex.In _value_i2 (Litex.Q (M := M)) := h_4881
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_4882)
            have h_4882 : Litex.In _value_i3 (Litex.Q (M := M)) := h_4882
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_4881) (Litex.rationalToComplex _value_i3 h_4882))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_4881) (Litex.rationalToComplex _value_i3 h_4882))
              exact (Litex.mulInQ _value_i2 _value_i3 h_4881 h_4882))));
          let _wd_2_1 := _value_i5;
          let _wd_2_2 := _value_i6;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3138 h_3139 True.intro))
          let _object_w12 := (Litex.mul _value_i5 _value_i6 (Litex.rationalToComplex _value_i5 h_3138) (Litex.rationalToComplex _value_i6 h_3139))
          have h_3117 : (by
            let _equal_wd_1_0 := _object_w11
            let _equal_wd_1_1 := _object_w12
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i6)])) = (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6)) from by
                    have _litex_residual : (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6)) = (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i6)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i6)])) = (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6)) from by
                    let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_6232 h_6233 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6232)
                      have h_6232 : Litex.In _value_i2 (Litex.Q (M := M)) := h_6232
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6233)
                      have h_6233 : Litex.In _value_i3 (Litex.Q (M := M)) := h_6233
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6232) (Litex.rationalToComplex _value_i3 h_6233))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6232) (Litex.rationalToComplex _value_i3 h_6233))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_6232 h_6233))));
                    let _wd_2_1 := _value_i5;
                    let _wd_2_2 := _value_i6;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3138 h_3139 True.intro))
                    let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_6399 h_6400 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6399)
                      have h_6399 : Litex.In _value_i2 (Litex.Q (M := M)) := h_6399
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6400)
                      have h_6400 : Litex.In _value_i3 (Litex.Q (M := M)) := h_6400
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6399) (Litex.rationalToComplex _value_i3 h_6400))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6399) (Litex.rationalToComplex _value_i3 h_6400))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_6399 h_6400))));
                    let _wd_2_1 := _value_i5;
                    let _wd_2_2 := _value_i6;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3138 h_3139 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          let _object_w13 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_6645 h_6646 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6645)
            have h_6645 : Litex.In _value_i2 (Litex.Q (M := M)) := h_6645
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6646)
            have h_6646 : Litex.In _value_i3 (Litex.Q (M := M)) := h_6646
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6645) (Litex.rationalToComplex _value_i3 h_6646))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6645) (Litex.rationalToComplex _value_i3 h_6646))
              exact (Litex.mulInQ _value_i2 _value_i3 h_6645 h_6646))));
          let _wd_2_1 := _object_w9;
          let _wd_2_2 := _value_i6;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
            let _atomic_wd_1_0 := _object_w9
            exact (Litex.inOfSame _object_w9 _object_w9 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w9) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w9))) h_3139 True.intro))
          let _object_w14 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_6859 h_6860 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6859)
            have h_6859 : Litex.In _value_i2 (Litex.Q (M := M)) := h_6859
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6860)
            have h_6860 : Litex.In _value_i3 (Litex.Q (M := M)) := h_6860
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6859) (Litex.rationalToComplex _value_i3 h_6860))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6859) (Litex.rationalToComplex _value_i3 h_6860))
              exact (Litex.mulInQ _value_i2 _value_i3 h_6859 h_6860))));
          let _wd_2_1 := _object_w10;
          let _wd_2_2 := _value_i6;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
            let _atomic_wd_1_0 := _object_w10
            exact (Litex.mulInQ _value_i4 _value_i5 h_3137 h_3138)) h_3139 True.intro))
          have h_3118 : (by
            let _equal_wd_1_0 := _object_w13
            let _equal_wd_1_1 := _object_w14
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) h_3116 (show @Eq M.Value _ _ from Eq.refl _)))
                )
            )
          let _object_w15 := (let _wd_2_0 := _object_w10;
          let _wd_2_1 := _value_i6;
          (Litex.mul _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _object_w10
            exact (Litex.mulInC _value_i4 _value_i5 (Litex.rationalToComplex _value_i4 h_3137) (Litex.rationalToComplex _value_i5 h_3138))) (Litex.rationalToComplex _wd_2_1 h_3139)))
          have h_3119 : (by
            let _equal_wd_1_0 := _object_w14
            let _equal_wd_1_1 := _object_w15
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)), (Litex.denote _value_i6)])) = (M.mulValue (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (Litex.denote _value_i6)) from by
                    have _litex_residual : (M.mulValue (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (Litex.denote _value_i6)) = (M.mulValue (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (Litex.denote _value_i6)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)), (Litex.denote _value_i6)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)), (Litex.denote _value_i6)])) = (M.mulValue (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (Litex.denote _value_i6)) from by
                    let _litex_original := _object_w14
                    let _litex_literal := _object_w14
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (Litex.denote _value_i6)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          let _object_w16 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_7983 h_7984 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_7983)
            have h_7983 : Litex.In _value_i2 (Litex.Q (M := M)) := h_7983
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_7984)
            have h_7984 : Litex.In _value_i3 (Litex.Q (M := M)) := h_7984
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_7983) (Litex.rationalToComplex _value_i3 h_7984))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_7983) (Litex.rationalToComplex _value_i3 h_7984))
              exact (Litex.mulInQ _value_i2 _value_i3 h_7983 h_7984))));
          let _wd_2_1 := _value_i4;
          let _wd_2_2 := _object_w11;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3137 (by
            let _atomic_wd_1_0 := _object_w11
            exact (Litex.inOfSame _object_w11 _object_w11 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w11) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w11))) True.intro))
          let _object_w17 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_8193 h_8194 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_8193)
            have h_8193 : Litex.In _value_i2 (Litex.Q (M := M)) := h_8193
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_8194)
            have h_8194 : Litex.In _value_i3 (Litex.Q (M := M)) := h_8194
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_8193) (Litex.rationalToComplex _value_i3 h_8194))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_8193) (Litex.rationalToComplex _value_i3 h_8194))
              exact (Litex.mulInQ _value_i2 _value_i3 h_8193 h_8194))));
          let _wd_2_1 := _value_i4;
          let _wd_2_2 := _object_w12;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3137 (by
            let _atomic_wd_1_0 := _object_w12
            exact (Litex.mulInQ _value_i5 _value_i6 h_3138 h_3139)) True.intro))
          have h_3120 : (by
            let _equal_wd_1_0 := _object_w16
            let _equal_wd_1_1 := _object_w17
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_3117))
                )
            )
          let _object_w18 := (let _wd_2_0 := _value_i4;
          let _wd_2_1 := _object_w12;
          (Litex.mul _wd_2_0 _wd_2_1 (Litex.rationalToComplex _wd_2_0 h_3137) (by
            let _atomic_wd_1_0 := _object_w12
            exact (Litex.mulInC _value_i5 _value_i6 (Litex.rationalToComplex _value_i5 h_3138) (Litex.rationalToComplex _value_i6 h_3139)))))
          have h_3121 : (by
            let _equal_wd_1_0 := _object_w17
            let _equal_wd_1_1 := _object_w18
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6))])) = (M.mulValue (Litex.denote _value_i4) (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6))) from by
                    have _litex_residual : (M.mulValue (Litex.denote _value_i4) (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6))) = (M.mulValue (Litex.denote _value_i4) (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6))])) = (M.mulValue (Litex.denote _value_i4) (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6))) from by
                    let _litex_original := _object_w17
                    let _litex_literal := _object_w17
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i4) (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6))) from rfl))
                  ))).trans _litex_residual)
                )
            )
          have h_3122 : (by
            let _equal_wd_1_0 := _object_w15
            let _equal_wd_1_1 := _object_w18
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i4 (Litex.rationalToComplex _value_i4 h_3137)) * (Litex.NativeBridge.asComplex _value_i5 (Litex.rationalToComplex _value_i5 h_3138))) * (Litex.NativeBridge.asComplex _value_i6 (Litex.rationalToComplex _value_i6 h_3139))) ((Litex.NativeBridge.asComplex _value_i4 (Litex.rationalToComplex _value_i4 h_3137)) * ((Litex.NativeBridge.asComplex _value_i5 (Litex.rationalToComplex _value_i5 h_3138)) * (Litex.NativeBridge.asComplex _value_i6 (Litex.rationalToComplex _value_i6 h_3139)))) (Litex.NativeBridge.denoteMul (_object_w15).val.left _value_i6 (_object_w15).wd.1 (_object_w15).wd.2 _ _ (Litex.NativeBridge.denoteMul _value_i4 _value_i5 (_object_w10).wd.1 (_object_w10).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.rationalToComplex _value_i4 h_3137)) (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.rationalToComplex _value_i5 h_3138))) (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.rationalToComplex _value_i6 h_3139))) (Litex.NativeBridge.denoteMul _value_i4 (_object_w18).val.right (_object_w18).wd.1 (_object_w18).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.rationalToComplex _value_i4 h_3137)) (Litex.NativeBridge.denoteMul _value_i5 _value_i6 (_object_w12).wd.1 (_object_w12).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.rationalToComplex _value_i5 h_3138)) (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.rationalToComplex _value_i6 h_3139)))) (by ring!))
                )
            )
          have h_3123 : (by
            let _equal_wd_1_0 := _object_w13
            let _equal_wd_1_1 := _object_w16
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  ((((((((h_3118).trans h_3119)).trans h_3122)).trans (h_3121).symm)).trans (h_3120).symm)
                )
            )
          exact (And.intro h_3116 (And.intro h_3117 (And.intro h_3118 (And.intro h_3119 (And.intro h_3120 (And.intro h_3121 (And.intro h_3122 h_3123)))))))
        );
        let h_9307 : (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact Litex.Subset _atomic_wd_1_0 (Litex.Q (M := M))) := (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact (by
            let _set := _atomic_wd_1_0
            exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Q (M := M)) _set.wd (by
            let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℚ) / (2 : ℚ)) (by norm_num)))) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Q (M := M)) _set.val.tail.wd (by
            let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℚ) / (3 : ℚ)) (by norm_num)))) (Litex.emptySubset (Litex.Q (M := M)))))));
        Litex.finiteFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True)) h_125 (Litex.formulaFnInFnSet _wd_1_1) (Litex.formulaFnInFnSet _wd_1_2) h_139 (fun i hi => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.rational) (Litex.denote (Litex.Q (M := M))) (M.standard_isSet Litex.StandardSetValue.rational) (Litex.isSet (Litex.Q (M := M))) (fun (_raw_i1 : M.Value) => True) i).mpr ⟨h_9307 i hi, True.intro⟩) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x1 _fold_h1 => (And.right (And.right (And.right (h_144 _fold_x0 _fold_h0 _fold_x1 _fold_h1)))))))) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x2 _fold_h2 => (And.right (And.right (And.right (And.right (And.right (And.right (And.right (h_3124 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2))))))))))))))))) = M.number ((1 : ℂ) / (3 : ℂ)) from (by
          let _fold := (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_1_0 := _wd_2_0
              let _atomic_wd_1_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _atomic_wd_1_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_1).wd.1 (_atomic_wd_1_1).wd.2.1 (_atomic_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0));
          let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_27 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_27)
            have h_27 : Litex.In _value_i1 (Litex.Q (M := M)) := h_27
            change Litex.In _value_i1 (Litex.Q (M := M))
            exact h_27));
          let _wd_1_2 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_46 h_47 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_46)
            have h_46 : Litex.In _value_i2 (Litex.Q (M := M)) := h_46
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_47)
            have h_47 : Litex.In _value_i3 (Litex.Q (M := M)) := h_47
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_46) (Litex.rationalToComplex _value_i3 h_47))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_46) (Litex.rationalToComplex _value_i3 h_47))
              exact (Litex.mulInQ _value_i2 _value_i3 h_46 h_47))));
          let _wd_1_3 := (Litex.number (M := M) (2 : ℂ));
          (let h_125 : (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
            let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
            (let _setElement_0 := _wd_2_0;
              let _setElement_1 := _wd_2_1;
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                let _atomic_wd_2_0 := _wd_2_0
                let _atomic_wd_2_1 := _wd_2_1
                exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0))
            exact Litex.IsFiniteSet _atomic_wd_1_0) := (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
            let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
            (let _setElement_0 := _wd_2_0;
              let _setElement_1 := _wd_2_1;
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                let _atomic_wd_2_0 := _wd_2_0
                let _atomic_wd_2_1 := _wd_2_1
                exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0))
            exact (let _finite_tail_0 := _atomic_wd_1_0;
            let _finite_tail_1 := _finite_tail_0.val.tail;
            let _finite_tail_2 := _finite_tail_1.val.tail;
            have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
            have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
            have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
            _finite_0));
          let h_139 : Litex.In _wd_1_3 (Litex.Q (M := M)) := (Litex.NativeBridge.numberInQOfEq (M := M) (2 : ℂ) (2 : ℚ) (by norm_num));
          let h_144 : ∀ {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_157 : Litex.In _value_i4 (Litex.Q (M := M))) {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_158 : Litex.In _value_i5 (Litex.Q (M := M))), (by
            let _object_w4 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_172 h_173 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_172)
              have h_172 : Litex.In _value_i2 (Litex.Q (M := M)) := h_172
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_173)
              have h_173 : Litex.In _value_i3 (Litex.Q (M := M)) := h_173
              change (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_172) (Litex.rationalToComplex _value_i3 h_173))
                exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_172) (Litex.rationalToComplex _value_i3 h_173))
                exact (Litex.mulInQ _value_i2 _value_i3 h_172 h_173))));
            let _wd_2_1 := _value_i4;
            let _wd_2_2 := _value_i5;
            (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_157 h_158 True.intro))
            let _object_w5 := (Litex.mul _value_i4 _value_i5 (Litex.rationalToComplex _value_i4 h_157) (Litex.rationalToComplex _value_i5 h_158))
            let _object_w6 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_1648 h_1649 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1648)
              have h_1648 : Litex.In _value_i2 (Litex.Q (M := M)) := h_1648
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1649)
              have h_1649 : Litex.In _value_i3 (Litex.Q (M := M)) := h_1649
              change (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_1648) (Litex.rationalToComplex _value_i3 h_1649))
                exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_1648) (Litex.rationalToComplex _value_i3 h_1649))
                exact (Litex.mulInQ _value_i2 _value_i3 h_1648 h_1649))));
            let _wd_2_1 := _value_i5;
            let _wd_2_2 := _value_i4;
            (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_158 h_157 True.intro))
            let _object_w7 := (Litex.mul _value_i5 _value_i4 (Litex.rationalToComplex _value_i5 h_158) (Litex.rationalToComplex _value_i4 h_157))
            exact (((by
              let _equal_wd_1_0 := _object_w4
              let _equal_wd_1_1 := _object_w5
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
              let _equal_wd_1_0 := _object_w6
              let _equal_wd_1_1 := _object_w7
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
              let _equal_wd_1_0 := _object_w5
              let _equal_wd_1_1 := _object_w7
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
              let _equal_wd_1_0 := _object_w4
              let _equal_wd_1_1 := _object_w6
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))
          ) := (by
            intro _Host_i4 _rep_i4 _value_i4 h_157 _Host_i5 _rep_i5 _value_i5 h_158
            let _object_w4 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_172 h_173 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_172)
              have h_172 : Litex.In _value_i2 (Litex.Q (M := M)) := h_172
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_173)
              have h_173 : Litex.In _value_i3 (Litex.Q (M := M)) := h_173
              change (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_172) (Litex.rationalToComplex _value_i3 h_173))
                exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_172) (Litex.rationalToComplex _value_i3 h_173))
                exact (Litex.mulInQ _value_i2 _value_i3 h_172 h_173))));
            let _wd_2_1 := _value_i4;
            let _wd_2_2 := _value_i5;
            (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_157 h_158 True.intro))
            let _object_w5 := (Litex.mul _value_i4 _value_i5 (Litex.rationalToComplex _value_i4 h_157) (Litex.rationalToComplex _value_i5 h_158))
            have h_140 : (by
              let _equal_wd_1_0 := _object_w4
              let _equal_wd_1_1 := _object_w5
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])) = (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from by
                      have _litex_residual : (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) = (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])) = (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from by
                      let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                        intro _raw_i2 _raw_i3 h_1299 h_1300 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1299)
                        have h_1299 : Litex.In _value_i2 (Litex.Q (M := M)) := h_1299
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1300)
                        have h_1300 : Litex.In _value_i3 (Litex.Q (M := M)) := h_1300
                        change (by
                          let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_1299) (Litex.rationalToComplex _value_i3 h_1300))
                          exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_1299) (Litex.rationalToComplex _value_i3 h_1300))
                          exact (Litex.mulInQ _value_i2 _value_i3 h_1299 h_1300))));
                      let _wd_2_1 := _value_i4;
                      let _wd_2_2 := _value_i5;
                      (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_157 h_158 True.intro))
                      let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                        intro _raw_i2 _raw_i3 h_1442 h_1443 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1442)
                        have h_1442 : Litex.In _value_i2 (Litex.Q (M := M)) := h_1442
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1443)
                        have h_1443 : Litex.In _value_i3 (Litex.Q (M := M)) := h_1443
                        change (by
                          let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_1442) (Litex.rationalToComplex _value_i3 h_1443))
                          exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_1442) (Litex.rationalToComplex _value_i3 h_1443))
                          exact (Litex.mulInQ _value_i2 _value_i3 h_1442 h_1443))));
                      let _wd_2_1 := _value_i4;
                      let _wd_2_2 := _value_i5;
                      (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_157 h_158 True.intro))
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from rfl))
                    ))).trans _litex_residual)
                  )
              )
            let _object_w6 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_1648 h_1649 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_1648)
              have h_1648 : Litex.In _value_i2 (Litex.Q (M := M)) := h_1648
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_1649)
              have h_1649 : Litex.In _value_i3 (Litex.Q (M := M)) := h_1649
              change (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_1648) (Litex.rationalToComplex _value_i3 h_1649))
                exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_1648) (Litex.rationalToComplex _value_i3 h_1649))
                exact (Litex.mulInQ _value_i2 _value_i3 h_1648 h_1649))));
            let _wd_2_1 := _value_i5;
            let _wd_2_2 := _value_i4;
            (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_158 h_157 True.intro))
            let _object_w7 := (Litex.mul _value_i5 _value_i4 (Litex.rationalToComplex _value_i5 h_158) (Litex.rationalToComplex _value_i4 h_157))
            have h_141 : (by
              let _equal_wd_1_0 := _object_w6
              let _equal_wd_1_1 := _object_w7
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i4)])) = (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i4)) from by
                      have _litex_residual : (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i4)) = (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i4)) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i4)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i4)])) = (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i4)) from by
                      let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                        intro _raw_i2 _raw_i3 h_2775 h_2776 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_2775)
                        have h_2775 : Litex.In _value_i2 (Litex.Q (M := M)) := h_2775
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_2776)
                        have h_2776 : Litex.In _value_i3 (Litex.Q (M := M)) := h_2776
                        change (by
                          let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_2775) (Litex.rationalToComplex _value_i3 h_2776))
                          exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_2775) (Litex.rationalToComplex _value_i3 h_2776))
                          exact (Litex.mulInQ _value_i2 _value_i3 h_2775 h_2776))));
                      let _wd_2_1 := _value_i5;
                      let _wd_2_2 := _value_i4;
                      (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_158 h_157 True.intro))
                      let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                        intro _raw_i2 _raw_i3 h_2918 h_2919 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_2918)
                        have h_2918 : Litex.In _value_i2 (Litex.Q (M := M)) := h_2918
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_2919)
                        have h_2919 : Litex.In _value_i3 (Litex.Q (M := M)) := h_2919
                        change (by
                          let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_2918) (Litex.rationalToComplex _value_i3 h_2919))
                          exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_2918) (Litex.rationalToComplex _value_i3 h_2919))
                          exact (Litex.mulInQ _value_i2 _value_i3 h_2918 h_2919))));
                      let _wd_2_1 := _value_i5;
                      let _wd_2_2 := _value_i4;
                      (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_158 h_157 True.intro))
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i4)) from rfl))
                    ))).trans _litex_residual)
                  )
              )
            have h_142 : (by
              let _equal_wd_1_0 := _object_w5
              let _equal_wd_1_1 := _object_w7
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i4 (Litex.rationalToComplex _value_i4 h_157)) * (Litex.NativeBridge.asComplex _value_i5 (Litex.rationalToComplex _value_i5 h_158))) ((Litex.NativeBridge.asComplex _value_i5 (Litex.rationalToComplex _value_i5 h_158)) * (Litex.NativeBridge.asComplex _value_i4 (Litex.rationalToComplex _value_i4 h_157))) (Litex.NativeBridge.denoteMul _value_i4 _value_i5 (_object_w5).wd.1 (_object_w5).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.rationalToComplex _value_i4 h_157)) (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.rationalToComplex _value_i5 h_158))) (Litex.NativeBridge.denoteMul _value_i5 _value_i4 (_object_w7).wd.1 (_object_w7).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.rationalToComplex _value_i5 h_158)) (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.rationalToComplex _value_i4 h_157))) (by ring!))
                  )
              )
            have h_143 : (by
              let _equal_wd_1_0 := _object_w4
              let _equal_wd_1_1 := _object_w6
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    ((((h_140).trans h_142)).trans (h_141).symm)
                  )
              )
            exact (And.intro h_140 (And.intro h_141 (And.intro h_142 h_143)))
          );
          let h_3124 : ∀ {_Host_i4 : Type _} [_rep_i4 : Litex.Representation M _Host_i4] (_value_i4 : Litex.Obj (M := M) _Host_i4) (h_3137 : Litex.In _value_i4 (Litex.Q (M := M))) {_Host_i5 : Type _} [_rep_i5 : Litex.Representation M _Host_i5] (_value_i5 : Litex.Obj (M := M) _Host_i5) (h_3138 : Litex.In _value_i5 (Litex.Q (M := M))) {_Host_i6 : Type _} [_rep_i6 : Litex.Representation M _Host_i6] (_value_i6 : Litex.Obj (M := M) _Host_i6) (h_3139 : Litex.In _value_i6 (Litex.Q (M := M))), (by
            let _object_w9 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_3153 h_3154 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3153)
              have h_3153 : Litex.In _value_i2 (Litex.Q (M := M)) := h_3153
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_3154)
              have h_3154 : Litex.In _value_i3 (Litex.Q (M := M)) := h_3154
              change (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_3153) (Litex.rationalToComplex _value_i3 h_3154))
                exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_3153) (Litex.rationalToComplex _value_i3 h_3154))
                exact (Litex.mulInQ _value_i2 _value_i3 h_3153 h_3154))));
            let _wd_2_1 := _value_i4;
            let _wd_2_2 := _value_i5;
            (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3137 h_3138 True.intro))
            let _object_w10 := (Litex.mul _value_i4 _value_i5 (Litex.rationalToComplex _value_i4 h_3137) (Litex.rationalToComplex _value_i5 h_3138))
            let _object_w11 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_4881 h_4882 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4881)
              have h_4881 : Litex.In _value_i2 (Litex.Q (M := M)) := h_4881
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_4882)
              have h_4882 : Litex.In _value_i3 (Litex.Q (M := M)) := h_4882
              change (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_4881) (Litex.rationalToComplex _value_i3 h_4882))
                exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_4881) (Litex.rationalToComplex _value_i3 h_4882))
                exact (Litex.mulInQ _value_i2 _value_i3 h_4881 h_4882))));
            let _wd_2_1 := _value_i5;
            let _wd_2_2 := _value_i6;
            (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3138 h_3139 True.intro))
            let _object_w12 := (Litex.mul _value_i5 _value_i6 (Litex.rationalToComplex _value_i5 h_3138) (Litex.rationalToComplex _value_i6 h_3139))
            let _object_w13 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_6645 h_6646 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6645)
              have h_6645 : Litex.In _value_i2 (Litex.Q (M := M)) := h_6645
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6646)
              have h_6646 : Litex.In _value_i3 (Litex.Q (M := M)) := h_6646
              change (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6645) (Litex.rationalToComplex _value_i3 h_6646))
                exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6645) (Litex.rationalToComplex _value_i3 h_6646))
                exact (Litex.mulInQ _value_i2 _value_i3 h_6645 h_6646))));
            let _wd_2_1 := _object_w9;
            let _wd_2_2 := _value_i6;
            (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
              let _atomic_wd_1_0 := _object_w9
              exact (Litex.inOfSame _object_w9 _object_w9 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w9) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w9))) h_3139 True.intro))
            let _object_w14 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_6859 h_6860 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6859)
              have h_6859 : Litex.In _value_i2 (Litex.Q (M := M)) := h_6859
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6860)
              have h_6860 : Litex.In _value_i3 (Litex.Q (M := M)) := h_6860
              change (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6859) (Litex.rationalToComplex _value_i3 h_6860))
                exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6859) (Litex.rationalToComplex _value_i3 h_6860))
                exact (Litex.mulInQ _value_i2 _value_i3 h_6859 h_6860))));
            let _wd_2_1 := _object_w10;
            let _wd_2_2 := _value_i6;
            (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
              let _atomic_wd_1_0 := _object_w10
              exact (Litex.mulInQ _value_i4 _value_i5 h_3137 h_3138)) h_3139 True.intro))
            let _object_w15 := (let _wd_2_0 := _object_w10;
            let _wd_2_1 := _value_i6;
            (Litex.mul _wd_2_0 _wd_2_1 (by
              let _atomic_wd_1_0 := _object_w10
              exact (Litex.mulInC _value_i4 _value_i5 (Litex.rationalToComplex _value_i4 h_3137) (Litex.rationalToComplex _value_i5 h_3138))) (Litex.rationalToComplex _wd_2_1 h_3139)))
            let _object_w16 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_7983 h_7984 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_7983)
              have h_7983 : Litex.In _value_i2 (Litex.Q (M := M)) := h_7983
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_7984)
              have h_7984 : Litex.In _value_i3 (Litex.Q (M := M)) := h_7984
              change (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_7983) (Litex.rationalToComplex _value_i3 h_7984))
                exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_7983) (Litex.rationalToComplex _value_i3 h_7984))
                exact (Litex.mulInQ _value_i2 _value_i3 h_7983 h_7984))));
            let _wd_2_1 := _value_i4;
            let _wd_2_2 := _object_w11;
            (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3137 (by
              let _atomic_wd_1_0 := _object_w11
              exact (Litex.inOfSame _object_w11 _object_w11 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w11) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w11))) True.intro))
            let _object_w17 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_8193 h_8194 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_8193)
              have h_8193 : Litex.In _value_i2 (Litex.Q (M := M)) := h_8193
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_8194)
              have h_8194 : Litex.In _value_i3 (Litex.Q (M := M)) := h_8194
              change (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_8193) (Litex.rationalToComplex _value_i3 h_8194))
                exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_8193) (Litex.rationalToComplex _value_i3 h_8194))
                exact (Litex.mulInQ _value_i2 _value_i3 h_8193 h_8194))));
            let _wd_2_1 := _value_i4;
            let _wd_2_2 := _object_w12;
            (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3137 (by
              let _atomic_wd_1_0 := _object_w12
              exact (Litex.mulInQ _value_i5 _value_i6 h_3138 h_3139)) True.intro))
            let _object_w18 := (let _wd_2_0 := _value_i4;
            let _wd_2_1 := _object_w12;
            (Litex.mul _wd_2_0 _wd_2_1 (Litex.rationalToComplex _wd_2_0 h_3137) (by
              let _atomic_wd_1_0 := _object_w12
              exact (Litex.mulInC _value_i5 _value_i6 (Litex.rationalToComplex _value_i5 h_3138) (Litex.rationalToComplex _value_i6 h_3139)))))
            exact (((by
              let _equal_wd_1_0 := _object_w9
              let _equal_wd_1_1 := _object_w10
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
              let _equal_wd_1_0 := _object_w11
              let _equal_wd_1_1 := _object_w12
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
              let _equal_wd_1_0 := _object_w13
              let _equal_wd_1_1 := _object_w14
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
              let _equal_wd_1_0 := _object_w14
              let _equal_wd_1_1 := _object_w15
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
              let _equal_wd_1_0 := _object_w16
              let _equal_wd_1_1 := _object_w17
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
              let _equal_wd_1_0 := _object_w17
              let _equal_wd_1_1 := _object_w18
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
              let _equal_wd_1_0 := _object_w15
              let _equal_wd_1_1 := _object_w18
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
              let _equal_wd_1_0 := _object_w13
              let _equal_wd_1_1 := _object_w16
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))))))))))
          ) := (by
            intro _Host_i4 _rep_i4 _value_i4 h_3137 _Host_i5 _rep_i5 _value_i5 h_3138 _Host_i6 _rep_i6 _value_i6 h_3139
            let _object_w9 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_3153 h_3154 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_3153)
              have h_3153 : Litex.In _value_i2 (Litex.Q (M := M)) := h_3153
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_3154)
              have h_3154 : Litex.In _value_i3 (Litex.Q (M := M)) := h_3154
              change (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_3153) (Litex.rationalToComplex _value_i3 h_3154))
                exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_3153) (Litex.rationalToComplex _value_i3 h_3154))
                exact (Litex.mulInQ _value_i2 _value_i3 h_3153 h_3154))));
            let _wd_2_1 := _value_i4;
            let _wd_2_2 := _value_i5;
            (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3137 h_3138 True.intro))
            let _object_w10 := (Litex.mul _value_i4 _value_i5 (Litex.rationalToComplex _value_i4 h_3137) (Litex.rationalToComplex _value_i5 h_3138))
            have h_3116 : (by
              let _equal_wd_1_0 := _object_w9
              let _equal_wd_1_1 := _object_w10
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])) = (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from by
                      have _litex_residual : (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) = (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (Litex.denote _value_i5)])) = (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from by
                      let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                        intro _raw_i2 _raw_i3 h_4476 h_4477 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4476)
                        have h_4476 : Litex.In _value_i2 (Litex.Q (M := M)) := h_4476
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_4477)
                        have h_4477 : Litex.In _value_i3 (Litex.Q (M := M)) := h_4477
                        change (by
                          let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_4476) (Litex.rationalToComplex _value_i3 h_4477))
                          exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_4476) (Litex.rationalToComplex _value_i3 h_4477))
                          exact (Litex.mulInQ _value_i2 _value_i3 h_4476 h_4477))));
                      let _wd_2_1 := _value_i4;
                      let _wd_2_2 := _value_i5;
                      (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3137 h_3138 True.intro))
                      let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                        intro _raw_i2 _raw_i3 h_4639 h_4640 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4639)
                        have h_4639 : Litex.In _value_i2 (Litex.Q (M := M)) := h_4639
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_4640)
                        have h_4640 : Litex.In _value_i3 (Litex.Q (M := M)) := h_4640
                        change (by
                          let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_4639) (Litex.rationalToComplex _value_i3 h_4640))
                          exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_4639) (Litex.rationalToComplex _value_i3 h_4640))
                          exact (Litex.mulInQ _value_i2 _value_i3 h_4639 h_4640))));
                      let _wd_2_1 := _value_i4;
                      let _wd_2_2 := _value_i5;
                      (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3137 h_3138 True.intro))
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) from rfl))
                    ))).trans _litex_residual)
                  )
              )
            let _object_w11 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_4881 h_4882 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_4881)
              have h_4881 : Litex.In _value_i2 (Litex.Q (M := M)) := h_4881
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_4882)
              have h_4882 : Litex.In _value_i3 (Litex.Q (M := M)) := h_4882
              change (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_4881) (Litex.rationalToComplex _value_i3 h_4882))
                exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_4881) (Litex.rationalToComplex _value_i3 h_4882))
                exact (Litex.mulInQ _value_i2 _value_i3 h_4881 h_4882))));
            let _wd_2_1 := _value_i5;
            let _wd_2_2 := _value_i6;
            (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3138 h_3139 True.intro))
            let _object_w12 := (Litex.mul _value_i5 _value_i6 (Litex.rationalToComplex _value_i5 h_3138) (Litex.rationalToComplex _value_i6 h_3139))
            have h_3117 : (by
              let _equal_wd_1_0 := _object_w11
              let _equal_wd_1_1 := _object_w12
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i6)])) = (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6)) from by
                      have _litex_residual : (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6)) = (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6)) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i6)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i5), (Litex.denote _value_i6)])) = (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6)) from by
                      let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                        intro _raw_i2 _raw_i3 h_6232 h_6233 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6232)
                        have h_6232 : Litex.In _value_i2 (Litex.Q (M := M)) := h_6232
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6233)
                        have h_6233 : Litex.In _value_i3 (Litex.Q (M := M)) := h_6233
                        change (by
                          let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6232) (Litex.rationalToComplex _value_i3 h_6233))
                          exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6232) (Litex.rationalToComplex _value_i3 h_6233))
                          exact (Litex.mulInQ _value_i2 _value_i3 h_6232 h_6233))));
                      let _wd_2_1 := _value_i5;
                      let _wd_2_2 := _value_i6;
                      (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3138 h_3139 True.intro))
                      let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                        intro _raw_i2 _raw_i3 h_6399 h_6400 _
                        let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6399)
                        have h_6399 : Litex.In _value_i2 (Litex.Q (M := M)) := h_6399
                        let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6400)
                        have h_6400 : Litex.In _value_i3 (Litex.Q (M := M)) := h_6400
                        change (by
                          let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6399) (Litex.rationalToComplex _value_i3 h_6400))
                          exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                        exact (by
                          let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6399) (Litex.rationalToComplex _value_i3 h_6400))
                          exact (Litex.mulInQ _value_i2 _value_i3 h_6399 h_6400))));
                      let _wd_2_1 := _value_i5;
                      let _wd_2_2 := _value_i6;
                      (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3138 h_3139 True.intro))
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6)) from rfl))
                    ))).trans _litex_residual)
                  )
              )
            let _object_w13 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_6645 h_6646 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6645)
              have h_6645 : Litex.In _value_i2 (Litex.Q (M := M)) := h_6645
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6646)
              have h_6646 : Litex.In _value_i3 (Litex.Q (M := M)) := h_6646
              change (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6645) (Litex.rationalToComplex _value_i3 h_6646))
                exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6645) (Litex.rationalToComplex _value_i3 h_6646))
                exact (Litex.mulInQ _value_i2 _value_i3 h_6645 h_6646))));
            let _wd_2_1 := _object_w9;
            let _wd_2_2 := _value_i6;
            (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
              let _atomic_wd_1_0 := _object_w9
              exact (Litex.inOfSame _object_w9 _object_w9 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w9) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w9))) h_3139 True.intro))
            let _object_w14 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_6859 h_6860 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_6859)
              have h_6859 : Litex.In _value_i2 (Litex.Q (M := M)) := h_6859
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_6860)
              have h_6860 : Litex.In _value_i3 (Litex.Q (M := M)) := h_6860
              change (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6859) (Litex.rationalToComplex _value_i3 h_6860))
                exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_6859) (Litex.rationalToComplex _value_i3 h_6860))
                exact (Litex.mulInQ _value_i2 _value_i3 h_6859 h_6860))));
            let _wd_2_1 := _object_w10;
            let _wd_2_2 := _value_i6;
            (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
              let _atomic_wd_1_0 := _object_w10
              exact (Litex.mulInQ _value_i4 _value_i5 h_3137 h_3138)) h_3139 True.intro))
            have h_3118 : (by
              let _equal_wd_1_0 := _object_w13
              let _equal_wd_1_1 := _object_w14
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) h_3116 (show @Eq M.Value _ _ from Eq.refl _)))
                  )
              )
            let _object_w15 := (let _wd_2_0 := _object_w10;
            let _wd_2_1 := _value_i6;
            (Litex.mul _wd_2_0 _wd_2_1 (by
              let _atomic_wd_1_0 := _object_w10
              exact (Litex.mulInC _value_i4 _value_i5 (Litex.rationalToComplex _value_i4 h_3137) (Litex.rationalToComplex _value_i5 h_3138))) (Litex.rationalToComplex _wd_2_1 h_3139)))
            have h_3119 : (by
              let _equal_wd_1_0 := _object_w14
              let _equal_wd_1_1 := _object_w15
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)), (Litex.denote _value_i6)])) = (M.mulValue (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (Litex.denote _value_i6)) from by
                      have _litex_residual : (M.mulValue (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (Litex.denote _value_i6)) = (M.mulValue (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (Litex.denote _value_i6)) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)), (Litex.denote _value_i6)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)), (Litex.denote _value_i6)])) = (M.mulValue (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (Litex.denote _value_i6)) from by
                      let _litex_original := _object_w14
                      let _litex_literal := _object_w14
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (M.mulValue (Litex.denote _value_i4) (Litex.denote _value_i5)) (Litex.denote _value_i6)) from rfl))
                    ))).trans _litex_residual)
                  )
              )
            let _object_w16 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_7983 h_7984 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_7983)
              have h_7983 : Litex.In _value_i2 (Litex.Q (M := M)) := h_7983
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_7984)
              have h_7984 : Litex.In _value_i3 (Litex.Q (M := M)) := h_7984
              change (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_7983) (Litex.rationalToComplex _value_i3 h_7984))
                exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_7983) (Litex.rationalToComplex _value_i3 h_7984))
                exact (Litex.mulInQ _value_i2 _value_i3 h_7983 h_7984))));
            let _wd_2_1 := _value_i4;
            let _wd_2_2 := _object_w11;
            (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3137 (by
              let _atomic_wd_1_0 := _object_w11
              exact (Litex.inOfSame _object_w11 _object_w11 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w11) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w11))) True.intro))
            let _object_w17 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
              intro _raw_i2 _raw_i3 h_8193 h_8194 _
              let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_8193)
              have h_8193 : Litex.In _value_i2 (Litex.Q (M := M)) := h_8193
              let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_8194)
              have h_8194 : Litex.In _value_i3 (Litex.Q (M := M)) := h_8194
              change (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_8193) (Litex.rationalToComplex _value_i3 h_8194))
                exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_8193) (Litex.rationalToComplex _value_i3 h_8194))
                exact (Litex.mulInQ _value_i2 _value_i3 h_8193 h_8194))));
            let _wd_2_1 := _value_i4;
            let _wd_2_2 := _object_w12;
            (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_3137 (by
              let _atomic_wd_1_0 := _object_w12
              exact (Litex.mulInQ _value_i5 _value_i6 h_3138 h_3139)) True.intro))
            have h_3120 : (by
              let _equal_wd_1_0 := _object_w16
              let _equal_wd_1_1 := _object_w17
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_3117))
                  )
              )
            let _object_w18 := (let _wd_2_0 := _value_i4;
            let _wd_2_1 := _object_w12;
            (Litex.mul _wd_2_0 _wd_2_1 (Litex.rationalToComplex _wd_2_0 h_3137) (by
              let _atomic_wd_1_0 := _object_w12
              exact (Litex.mulInC _value_i5 _value_i6 (Litex.rationalToComplex _value_i5 h_3138) (Litex.rationalToComplex _value_i6 h_3139)))))
            have h_3121 : (by
              let _equal_wd_1_0 := _object_w17
              let _equal_wd_1_1 := _object_w18
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6))])) = (M.mulValue (Litex.denote _value_i4) (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6))) from by
                      have _litex_residual : (M.mulValue (Litex.denote _value_i4) (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6))) = (M.mulValue (Litex.denote _value_i4) (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6))) := (show @Eq M.Value _ _ from Eq.refl _)
                      exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i4), (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6))])) = (M.mulValue (Litex.denote _value_i4) (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6))) from by
                      let _litex_original := _object_w17
                      let _litex_literal := _object_w17
                      have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                      have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                      exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i4) (M.mulValue (Litex.denote _value_i5) (Litex.denote _value_i6))) from rfl))
                    ))).trans _litex_residual)
                  )
              )
            have h_3122 : (by
              let _equal_wd_1_0 := _object_w15
              let _equal_wd_1_1 := _object_w18
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i4 (Litex.rationalToComplex _value_i4 h_3137)) * (Litex.NativeBridge.asComplex _value_i5 (Litex.rationalToComplex _value_i5 h_3138))) * (Litex.NativeBridge.asComplex _value_i6 (Litex.rationalToComplex _value_i6 h_3139))) ((Litex.NativeBridge.asComplex _value_i4 (Litex.rationalToComplex _value_i4 h_3137)) * ((Litex.NativeBridge.asComplex _value_i5 (Litex.rationalToComplex _value_i5 h_3138)) * (Litex.NativeBridge.asComplex _value_i6 (Litex.rationalToComplex _value_i6 h_3139)))) (Litex.NativeBridge.denoteMul (_object_w15).val.left _value_i6 (_object_w15).wd.1 (_object_w15).wd.2 _ _ (Litex.NativeBridge.denoteMul _value_i4 _value_i5 (_object_w10).wd.1 (_object_w10).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.rationalToComplex _value_i4 h_3137)) (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.rationalToComplex _value_i5 h_3138))) (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.rationalToComplex _value_i6 h_3139))) (Litex.NativeBridge.denoteMul _value_i4 (_object_w18).val.right (_object_w18).wd.1 (_object_w18).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i4 (Litex.rationalToComplex _value_i4 h_3137)) (Litex.NativeBridge.denoteMul _value_i5 _value_i6 (_object_w12).wd.1 (_object_w12).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i5 (Litex.rationalToComplex _value_i5 h_3138)) (Litex.NativeBridge.asComplex_spec _value_i6 (Litex.rationalToComplex _value_i6 h_3139)))) (by ring!))
                  )
              )
            have h_3123 : (by
              let _equal_wd_1_0 := _object_w13
              let _equal_wd_1_1 := _object_w16
              exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
              (by
                litex_checked_step =>
                  exact (
                    ((((((((h_3118).trans h_3119)).trans h_3122)).trans (h_3121).symm)).trans (h_3120).symm)
                  )
              )
            exact (And.intro h_3116 (And.intro h_3117 (And.intro h_3118 (And.intro h_3119 (And.intro h_3120 (And.intro h_3121 (And.intro h_3122 h_3123)))))))
          );
          let h_9307 : (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
            let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
            (let _setElement_0 := _wd_2_0;
              let _setElement_1 := _wd_2_1;
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                let _atomic_wd_2_0 := _wd_2_0
                let _atomic_wd_2_1 := _wd_2_1
                exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0))
            exact Litex.Subset _atomic_wd_1_0 (Litex.Q (M := M))) := (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
            let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
            (let _setElement_0 := _wd_2_0;
              let _setElement_1 := _wd_2_1;
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                let _atomic_wd_2_0 := _wd_2_0
                let _atomic_wd_2_1 := _wd_2_1
                exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0))
            exact (by
              let _set := _atomic_wd_1_0
              exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Q (M := M)) _set.wd (by
              let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℚ) / (2 : ℚ)) (by norm_num)))) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Q (M := M)) _set.val.tail.wd (by
              let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℚ) / (3 : ℚ)) (by norm_num)))) (Litex.emptySubset (Litex.Q (M := M)))))));
          Litex.finiteFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True)) h_125 (Litex.formulaFnInFnSet _wd_1_1) (Litex.formulaFnInFnSet _wd_1_2) h_139 (fun i hi => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.rational) (Litex.denote (Litex.Q (M := M))) (M.standard_isSet Litex.StandardSetValue.rational) (Litex.isSet (Litex.Q (M := M))) (fun (_raw_i1 : M.Value) => True) i).mpr ⟨h_9307 i hi, True.intro⟩) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x1 _fold_h1 => (And.right (And.right (And.right (h_144 _fold_x0 _fold_h0 _fold_x1 _fold_h1)))))))) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x2 _fold_h2 => (And.right (And.right (And.right (And.right (And.right (And.right (And.right (h_3124 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2))))))))))))))))
          have _seed : Litex.denote _fold.val.seed = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
          have _members : ∀ x, M.mem x (Litex.denote _fold.val.set) ↔ x ∈ ([M.number ((1 : ℂ) / (2 : ℂ)), M.number ((1 : ℂ) / (3 : ℂ))] : List M.Value) := (by
            let _enumerated := (let _wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
            let _wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
            (let _setElement_0 := _wd_1_0;
              let _setElement_1 := _wd_1_1;
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                let _atomic_wd_1_0 := _wd_1_0
                let _atomic_wd_1_1 := _wd_1_1
                exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _atomic_wd_1_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_1).wd.1 (_atomic_wd_1_1).wd.2.1 (_atomic_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0))
            have _enumeration_same : Litex.Same (let _wd_1_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
            let _wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
            (let _setElement_0 := _wd_1_0;
              let _setElement_1 := _wd_1_1;
              let _setTail_2 := Litex.emptySet (M := M);
              let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
              let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
              let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
                let _atomic_wd_1_0 := _wd_1_0
                let _atomic_wd_1_1 := _wd_1_1
                exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _atomic_wd_1_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_1).wd.1 (_atomic_wd_1_1).wd.2.1 (_atomic_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
              let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
              _setTail_0)) _enumerated := (show @Eq M.Value _ _ from Eq.refl _)
            let _collection_tail_0 := _enumerated
            let _collection_tail_1 := _collection_tail_0.val.tail
            let _collection_tail_2 := _collection_tail_1.val.tail
            have _members_2 : ∀ x, M.mem x (Litex.denote _collection_tail_2) ↔ x ∈ ([] : List M.Value) := Litex.finiteMembersEmpty
            have _number_1 : Litex.denote _collection_tail_1.val.element = M.number ((1 : ℂ) / (3 : ℂ)) := ((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (3 : ℂ)) = ((1 : ℂ) / (3 : ℂ))))
            have _members_1 := Litex.finiteMembersInsert _collection_tail_1 (M.number ((1 : ℂ) / (3 : ℂ))) [] _number_1 _members_2
            have _number_0 : Litex.denote _collection_tail_0.val.element = M.number ((1 : ℂ) / (2 : ℂ)) := ((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (2 : ℂ)) = ((1 : ℂ) / (2 : ℂ))))
            have _members_0 := Litex.finiteMembersInsert _collection_tail_0 (M.number ((1 : ℂ) / (2 : ℂ))) [M.number ((1 : ℂ) / (3 : ℂ))] _number_0 _members_1
            intro x
            exact Eq.mpr (congrArg (fun _set => M.mem x _set ↔ x ∈ ([M.number ((1 : ℂ) / (2 : ℂ)), M.number ((1 : ℂ) / (3 : ℂ))] : List M.Value)) _enumeration_same) (_members_0 x))
          have _distinct : ([M.number ((1 : ℂ) / (2 : ℂ)), M.number ((1 : ℂ) / (3 : ℂ))] : List M.Value).Nodup := List.Nodup.map M.number_injective (by norm_num : ([((1 : ℂ) / (2 : ℂ)), ((1 : ℂ) / (3 : ℂ))] : List ℂ).Nodup)
          have _term_0 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.function) (M.number ((1 : ℂ) / (2 : ℂ))) = M.number ((1 : ℂ) / (2 : ℂ)) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_18670 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_18670)
            have h_18670 : Litex.In _value_i1 (Litex.Q (M := M)) := h_18670
            change Litex.In _value_i1 (Litex.Q (M := M))
            exact h_18670));
          let _object_w38 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True) _wd_1_0 _object_w38 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_0 := _object_w38
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_w38).wd.1 (_object_w38).wd.2.1 (_object_w38).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℚ) / (2 : ℚ)) (by norm_num)))) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_18670 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_18670)
            have h_18670 : Litex.In _value_i1 (Litex.Q (M := M)) := h_18670
            change Litex.In _value_i1 (Litex.Q (M := M))
            exact h_18670))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.argument = M.number ((1 : ℂ) / (2 : ℂ)) := ((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (2 : ℂ)) = ((1 : ℂ) / (2 : ℂ))))
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) := by change (fun (_raw_i1 : M.Value) => _raw_i1) (Litex.denote _call.val.argument) = (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))); norm_num [_argument_0, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ))) = M.number ((1 : ℂ) / (2 : ℂ)) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument_0).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _step_0 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.operation) (Litex.FiniteFunction.pack2 (M.number (2 : ℂ)) (M.number ((1 : ℂ) / (2 : ℂ)))) = M.number (1 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_18693 h_18694 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_18693)
            have h_18693 : Litex.In _value_i2 (Litex.Q (M := M)) := h_18693
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_18694)
            have h_18694 : Litex.In _value_i3 (Litex.Q (M := M)) := h_18694
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_18693) (Litex.rationalToComplex _value_i3 h_18694))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_18693) (Litex.rationalToComplex _value_i3 h_18694))
              exact (Litex.mulInQ _value_i2 _value_i3 h_18693 h_18694))));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          let _object_w40 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 _object_w40 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInQOfEq (M := M) (2 : ℂ) (2 : ℚ) (by norm_num)) (by
            let _atomic_wd_1_0 := _object_w40
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_object_w40).wd.1 (_object_w40).wd.2.1 (_object_w40).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℚ) / (2 : ℚ)) (by norm_num)))) True.intro))
            let _literal := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_18693 h_18694 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_18693)
            have h_18693 : Litex.In _value_i2 (Litex.Q (M := M)) := h_18693
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_18694)
            have h_18694 : Litex.In _value_i3 (Litex.Q (M := M)) := h_18694
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_18693) (Litex.rationalToComplex _value_i3 h_18694))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_18693) (Litex.rationalToComplex _value_i3 h_18694))
              exact (Litex.mulInQ _value_i2 _value_i3 h_18693 h_18694))))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _ _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.first = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            have _argument_1 : Litex.denote _call.val.second = M.number ((1 : ℂ) / (2 : ℂ)) := ((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (2 : ℂ)) = ((1 : ℂ) / (2 : ℂ))))
            have _body : _literal.val.bodyValue (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) = (M.mulValue (M.number (2 : ℂ)) (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ)))) := by change (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).1 (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).2 = (M.mulValue (M.number (2 : ℂ)) (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ)))); norm_num [Litex.FiniteFunction.unpack_pack2, _argument_0, _argument_1, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.mulValue (M.number (2 : ℂ)) (M.divValue (M.number (1 : ℂ)) (M.number (2 : ℂ)))) = M.number (1 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) _argument_0 _argument_1)).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _term_1 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.function) (M.number ((1 : ℂ) / (3 : ℂ))) = M.number ((1 : ℂ) / (3 : ℂ)) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_18790 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_18790)
            have h_18790 : Litex.In _value_i1 (Litex.Q (M := M)) := h_18790
            change Litex.In _value_i1 (Litex.Q (M := M))
            exact h_18790));
          let _object_w42 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (Litex.call Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True) _wd_1_0 _object_w42 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_0 := _object_w42
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_object_w42).wd.1 (_object_w42).wd.2.1 (_object_w42).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℚ) / (3 : ℚ)) (by norm_num)))) True.intro))
            let _literal := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_18790 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_18790)
            have h_18790 : Litex.In _value_i1 (Litex.Q (M := M)) := h_18790
            change Litex.In _value_i1 (Litex.Q (M := M))
            exact h_18790))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.argument = M.number ((1 : ℂ) / (3 : ℂ)) := ((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (3 : ℂ)) = ((1 : ℂ) / (3 : ℂ))))
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.divValue (M.number (1 : ℂ)) (M.number (3 : ℂ))) := by change (fun (_raw_i1 : M.Value) => _raw_i1) (Litex.denote _call.val.argument) = (M.divValue (M.number (1 : ℂ)) (M.number (3 : ℂ))); norm_num [_argument_0, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.divValue (M.number (1 : ℂ)) (M.number (3 : ℂ))) = M.number ((1 : ℂ) / (3 : ℂ)) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument_0).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _step_1 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.operation) (Litex.FiniteFunction.pack2 (M.number (1 : ℂ)) (M.number ((1 : ℂ) / (3 : ℂ)))) = M.number ((1 : ℂ) / (3 : ℂ)) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_18813 h_18814 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_18813)
            have h_18813 : Litex.In _value_i2 (Litex.Q (M := M)) := h_18813
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_18814)
            have h_18814 : Litex.In _value_i3 (Litex.Q (M := M)) := h_18814
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_18813) (Litex.rationalToComplex _value_i3 h_18814))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_18813) (Litex.rationalToComplex _value_i3 h_18814))
              exact (Litex.mulInQ _value_i2 _value_i3 h_18813 h_18814))));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          let _object_w44 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 _object_w44 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInQOfEq (M := M) (1 : ℂ) (1 : ℚ) (by norm_num)) (by
            let _atomic_wd_1_0 := _object_w44
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 ((1 : ℂ) / (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_object_w44).wd.1 (_object_w44).wd.2.1 (_object_w44).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℚ) / (3 : ℚ)) (by norm_num)))) True.intro))
            let _literal := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_18813 h_18814 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_18813)
            have h_18813 : Litex.In _value_i2 (Litex.Q (M := M)) := h_18813
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_18814)
            have h_18814 : Litex.In _value_i3 (Litex.Q (M := M)) := h_18814
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_18813) (Litex.rationalToComplex _value_i3 h_18814))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_18813) (Litex.rationalToComplex _value_i3 h_18814))
              exact (Litex.mulInQ _value_i2 _value_i3 h_18813 h_18814))))
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _ _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.first = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
            have _argument_1 : Litex.denote _call.val.second = M.number ((1 : ℂ) / (3 : ℂ)) := ((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (3 : ℂ)) = ((1 : ℂ) / (3 : ℂ))))
            have _body : _literal.val.bodyValue (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) = (M.mulValue (M.number (1 : ℂ)) (M.divValue (M.number (1 : ℂ)) (M.number (3 : ℂ)))) := by change (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).1 (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).2 = (M.mulValue (M.number (1 : ℂ)) (M.divValue (M.number (1 : ℂ)) (M.number (3 : ℂ)))); norm_num [Litex.FiniteFunction.unpack_pack2, _argument_0, _argument_1, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.mulValue (M.number (1 : ℂ)) (M.divValue (M.number (1 : ℂ)) (M.number (3 : ℂ)))) = M.number ((1 : ℂ) / (3 : ℂ)) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) _argument_0 _argument_1)).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          apply (Litex.finiteFoldEnumerate _fold [M.number ((1 : ℂ) / (2 : ℂ)), M.number ((1 : ℂ) / (3 : ℂ))] _distinct _members).trans
          show Litex.foldValue [M.number ((1 : ℂ) / (2 : ℂ)), M.number ((1 : ℂ) / (3 : ℂ))] (Litex.denote _fold.val.function) (Litex.denote _fold.val.operation) (Litex.denote _fold.val.seed) = M.number ((1 : ℂ) / (3 : ℂ))
          norm_num [Litex.foldValue, Litex.foldApply2, _seed, _term_0, _step_0, _term_1, _step_1]))).trans (((Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_equal_wd_1_1).wd.1 (_equal_wd_1_1).wd.2.1 (_equal_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : ((1 : ℂ) / (3 : ℂ)) = ((1 : ℂ) / (3 : ℂ))))).symm)))
      )
  )

noncomputable def _object_w104 := (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
(let _setElement_0 := _wd_2_0;
  let _setElement_1 := _wd_2_1;
  let _setTail_2 := Litex.emptySet (M := M);
  let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
  let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
  let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
    let _atomic_wd_1_0 := _wd_2_0
    let _atomic_wd_1_1 := _wd_2_1
    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _atomic_wd_1_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
  let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
  _setTail_0));
let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i13 : M.Value) => True) (fun (_raw_i13 : M.Value) => _raw_i13) (by
  intro _raw_i13 h_28250 _
  let _value_i13 := Litex.semanticObject (M := M) _raw_i13 (M.member_isSet h_28250)
  have h_28250 : Litex.In _value_i13 (Litex.Q (M := M)) := h_28250
  change Litex.In _value_i13 (Litex.Q (M := M))
  exact h_28250));
let _wd_1_2 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by
  intro _raw_i14 _raw_i15 h_28269 h_28270 _
  let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_28269)
  have h_28269 : Litex.In _value_i14 (Litex.Q (M := M)) := h_28269
  let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_28270)
  have h_28270 : Litex.In _value_i15 (Litex.Q (M := M)) := h_28270
  change (by
    let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_28269) (Litex.rationalToComplex _value_i15 h_28270))
    exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_28269) (Litex.rationalToComplex _value_i15 h_28270))
    exact (Litex.mulInQ _value_i14 _value_i15 h_28269 h_28270))));
let _wd_1_3 := (Litex.number (M := M) (2 : ℂ));
(let h_28348 : (by
  let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  (let _setElement_0 := _wd_2_0;
    let _setElement_1 := _wd_2_1;
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
      let _atomic_wd_2_0 := _wd_2_0
      let _atomic_wd_2_1 := _wd_2_1
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0))
  exact Litex.IsFiniteSet _atomic_wd_1_0) := (by
  let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  (let _setElement_0 := _wd_2_0;
    let _setElement_1 := _wd_2_1;
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
      let _atomic_wd_2_0 := _wd_2_0
      let _atomic_wd_2_1 := _wd_2_1
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0))
  exact (let _finite_tail_0 := _atomic_wd_1_0;
  let _finite_tail_1 := _finite_tail_0.val.tail;
  let _finite_tail_2 := _finite_tail_1.val.tail;
  have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
  have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
  have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
  _finite_0));
let h_28356 : Litex.In _wd_1_3 (Litex.Q (M := M)) := (Litex.NativeBridge.numberInQOfEq (M := M) (2 : ℂ) (2 : ℚ) (by norm_num));
let h_28361 : ∀ {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_28374 : Litex.In _value_i16 (Litex.Q (M := M))) {_Host_i17 : Type _} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_28375 : Litex.In _value_i17 (Litex.Q (M := M))), (by
  let _object_w68 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by
    intro _raw_i14 _raw_i15 h_28389 h_28390 _
    let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_28389)
    have h_28389 : Litex.In _value_i14 (Litex.Q (M := M)) := h_28389
    let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_28390)
    have h_28390 : Litex.In _value_i15 (Litex.Q (M := M)) := h_28390
    change (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_28389) (Litex.rationalToComplex _value_i15 h_28390))
      exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_28389) (Litex.rationalToComplex _value_i15 h_28390))
      exact (Litex.mulInQ _value_i14 _value_i15 h_28389 h_28390))));
  let _wd_2_1 := _value_i16;
  let _wd_2_2 := _value_i17;
  (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_28374 h_28375 True.intro))
  let _object_w69 := (Litex.mul _value_i16 _value_i17 (Litex.rationalToComplex _value_i16 h_28374) (Litex.rationalToComplex _value_i17 h_28375))
  let _object_w70 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by
    intro _raw_i14 _raw_i15 h_29865 h_29866 _
    let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_29865)
    have h_29865 : Litex.In _value_i14 (Litex.Q (M := M)) := h_29865
    let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_29866)
    have h_29866 : Litex.In _value_i15 (Litex.Q (M := M)) := h_29866
    change (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_29865) (Litex.rationalToComplex _value_i15 h_29866))
      exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_29865) (Litex.rationalToComplex _value_i15 h_29866))
      exact (Litex.mulInQ _value_i14 _value_i15 h_29865 h_29866))));
  let _wd_2_1 := _value_i17;
  let _wd_2_2 := _value_i16;
  (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_28375 h_28374 True.intro))
  let _object_w71 := (Litex.mul _value_i17 _value_i16 (Litex.rationalToComplex _value_i17 h_28375) (Litex.rationalToComplex _value_i16 h_28374))
  exact (((by
    let _equal_wd_1_0 := _object_w68
    let _equal_wd_1_1 := _object_w69
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w70
    let _equal_wd_1_1 := _object_w71
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w69
    let _equal_wd_1_1 := _object_w71
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w68
    let _equal_wd_1_1 := _object_w70
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))
) := (by
  intro _Host_i16 _rep_i16 _value_i16 h_28374 _Host_i17 _rep_i17 _value_i17 h_28375
  let _object_w68 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by
    intro _raw_i14 _raw_i15 h_28389 h_28390 _
    let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_28389)
    have h_28389 : Litex.In _value_i14 (Litex.Q (M := M)) := h_28389
    let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_28390)
    have h_28390 : Litex.In _value_i15 (Litex.Q (M := M)) := h_28390
    change (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_28389) (Litex.rationalToComplex _value_i15 h_28390))
      exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_28389) (Litex.rationalToComplex _value_i15 h_28390))
      exact (Litex.mulInQ _value_i14 _value_i15 h_28389 h_28390))));
  let _wd_2_1 := _value_i16;
  let _wd_2_2 := _value_i17;
  (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_28374 h_28375 True.intro))
  let _object_w69 := (Litex.mul _value_i16 _value_i17 (Litex.rationalToComplex _value_i16 h_28374) (Litex.rationalToComplex _value_i17 h_28375))
  have h_28357 : (by
    let _equal_wd_1_0 := _object_w68
    let _equal_wd_1_1 := _object_w69
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i16), (Litex.denote _value_i17)])) = (M.mulValue (Litex.denote _value_i16) (Litex.denote _value_i17)) from by
            have _litex_residual : (M.mulValue (Litex.denote _value_i16) (Litex.denote _value_i17)) = (M.mulValue (Litex.denote _value_i16) (Litex.denote _value_i17)) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i16), (Litex.denote _value_i17)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i16), (Litex.denote _value_i17)])) = (M.mulValue (Litex.denote _value_i16) (Litex.denote _value_i17)) from by
            let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by
              intro _raw_i14 _raw_i15 h_29516 h_29517 _
              let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_29516)
              have h_29516 : Litex.In _value_i14 (Litex.Q (M := M)) := h_29516
              let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_29517)
              have h_29517 : Litex.In _value_i15 (Litex.Q (M := M)) := h_29517
              change (by
                let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_29516) (Litex.rationalToComplex _value_i15 h_29517))
                exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_29516) (Litex.rationalToComplex _value_i15 h_29517))
                exact (Litex.mulInQ _value_i14 _value_i15 h_29516 h_29517))));
            let _wd_2_1 := _value_i16;
            let _wd_2_2 := _value_i17;
            (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_28374 h_28375 True.intro))
            let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by
              intro _raw_i14 _raw_i15 h_29659 h_29660 _
              let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_29659)
              have h_29659 : Litex.In _value_i14 (Litex.Q (M := M)) := h_29659
              let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_29660)
              have h_29660 : Litex.In _value_i15 (Litex.Q (M := M)) := h_29660
              change (by
                let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_29659) (Litex.rationalToComplex _value_i15 h_29660))
                exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_29659) (Litex.rationalToComplex _value_i15 h_29660))
                exact (Litex.mulInQ _value_i14 _value_i15 h_29659 h_29660))));
            let _wd_2_1 := _value_i16;
            let _wd_2_2 := _value_i17;
            (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_28374 h_28375 True.intro))
            have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
            have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i16) (Litex.denote _value_i17)) from rfl))
          ))).trans _litex_residual)
        )
    )
  let _object_w70 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by
    intro _raw_i14 _raw_i15 h_29865 h_29866 _
    let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_29865)
    have h_29865 : Litex.In _value_i14 (Litex.Q (M := M)) := h_29865
    let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_29866)
    have h_29866 : Litex.In _value_i15 (Litex.Q (M := M)) := h_29866
    change (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_29865) (Litex.rationalToComplex _value_i15 h_29866))
      exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_29865) (Litex.rationalToComplex _value_i15 h_29866))
      exact (Litex.mulInQ _value_i14 _value_i15 h_29865 h_29866))));
  let _wd_2_1 := _value_i17;
  let _wd_2_2 := _value_i16;
  (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_28375 h_28374 True.intro))
  let _object_w71 := (Litex.mul _value_i17 _value_i16 (Litex.rationalToComplex _value_i17 h_28375) (Litex.rationalToComplex _value_i16 h_28374))
  have h_28358 : (by
    let _equal_wd_1_0 := _object_w70
    let _equal_wd_1_1 := _object_w71
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i17), (Litex.denote _value_i16)])) = (M.mulValue (Litex.denote _value_i17) (Litex.denote _value_i16)) from by
            have _litex_residual : (M.mulValue (Litex.denote _value_i17) (Litex.denote _value_i16)) = (M.mulValue (Litex.denote _value_i17) (Litex.denote _value_i16)) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i17), (Litex.denote _value_i16)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i17), (Litex.denote _value_i16)])) = (M.mulValue (Litex.denote _value_i17) (Litex.denote _value_i16)) from by
            let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by
              intro _raw_i14 _raw_i15 h_30992 h_30993 _
              let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_30992)
              have h_30992 : Litex.In _value_i14 (Litex.Q (M := M)) := h_30992
              let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_30993)
              have h_30993 : Litex.In _value_i15 (Litex.Q (M := M)) := h_30993
              change (by
                let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_30992) (Litex.rationalToComplex _value_i15 h_30993))
                exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_30992) (Litex.rationalToComplex _value_i15 h_30993))
                exact (Litex.mulInQ _value_i14 _value_i15 h_30992 h_30993))));
            let _wd_2_1 := _value_i17;
            let _wd_2_2 := _value_i16;
            (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_28375 h_28374 True.intro))
            let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by
              intro _raw_i14 _raw_i15 h_31135 h_31136 _
              let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_31135)
              have h_31135 : Litex.In _value_i14 (Litex.Q (M := M)) := h_31135
              let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_31136)
              have h_31136 : Litex.In _value_i15 (Litex.Q (M := M)) := h_31136
              change (by
                let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_31135) (Litex.rationalToComplex _value_i15 h_31136))
                exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_31135) (Litex.rationalToComplex _value_i15 h_31136))
                exact (Litex.mulInQ _value_i14 _value_i15 h_31135 h_31136))));
            let _wd_2_1 := _value_i17;
            let _wd_2_2 := _value_i16;
            (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_28375 h_28374 True.intro))
            have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
            have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i17) (Litex.denote _value_i16)) from rfl))
          ))).trans _litex_residual)
        )
    )
  have h_28359 : (by
    let _equal_wd_1_0 := _object_w69
    let _equal_wd_1_1 := _object_w71
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i16 (Litex.rationalToComplex _value_i16 h_28374)) * (Litex.NativeBridge.asComplex _value_i17 (Litex.rationalToComplex _value_i17 h_28375))) ((Litex.NativeBridge.asComplex _value_i17 (Litex.rationalToComplex _value_i17 h_28375)) * (Litex.NativeBridge.asComplex _value_i16 (Litex.rationalToComplex _value_i16 h_28374))) (Litex.NativeBridge.denoteMul _value_i16 _value_i17 (_object_w69).wd.1 (_object_w69).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i16 (Litex.rationalToComplex _value_i16 h_28374)) (Litex.NativeBridge.asComplex_spec _value_i17 (Litex.rationalToComplex _value_i17 h_28375))) (Litex.NativeBridge.denoteMul _value_i17 _value_i16 (_object_w71).wd.1 (_object_w71).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i17 (Litex.rationalToComplex _value_i17 h_28375)) (Litex.NativeBridge.asComplex_spec _value_i16 (Litex.rationalToComplex _value_i16 h_28374))) (by ring!))
        )
    )
  have h_28360 : (by
    let _equal_wd_1_0 := _object_w68
    let _equal_wd_1_1 := _object_w70
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          ((((h_28357).trans h_28359)).trans (h_28358).symm)
        )
    )
  exact (And.intro h_28357 (And.intro h_28358 (And.intro h_28359 h_28360)))
);
let h_31341 : ∀ {_Host_i16 : Type _} [_rep_i16 : Litex.Representation M _Host_i16] (_value_i16 : Litex.Obj (M := M) _Host_i16) (h_31354 : Litex.In _value_i16 (Litex.Q (M := M))) {_Host_i17 : Type _} [_rep_i17 : Litex.Representation M _Host_i17] (_value_i17 : Litex.Obj (M := M) _Host_i17) (h_31355 : Litex.In _value_i17 (Litex.Q (M := M))) {_Host_i18 : Type _} [_rep_i18 : Litex.Representation M _Host_i18] (_value_i18 : Litex.Obj (M := M) _Host_i18) (h_31356 : Litex.In _value_i18 (Litex.Q (M := M))), (by
  let _object_w73 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by
    intro _raw_i14 _raw_i15 h_31370 h_31371 _
    let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_31370)
    have h_31370 : Litex.In _value_i14 (Litex.Q (M := M)) := h_31370
    let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_31371)
    have h_31371 : Litex.In _value_i15 (Litex.Q (M := M)) := h_31371
    change (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_31370) (Litex.rationalToComplex _value_i15 h_31371))
      exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_31370) (Litex.rationalToComplex _value_i15 h_31371))
      exact (Litex.mulInQ _value_i14 _value_i15 h_31370 h_31371))));
  let _wd_2_1 := _value_i16;
  let _wd_2_2 := _value_i17;
  (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_31354 h_31355 True.intro))
  let _object_w74 := (Litex.mul _value_i16 _value_i17 (Litex.rationalToComplex _value_i16 h_31354) (Litex.rationalToComplex _value_i17 h_31355))
  let _object_w75 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by
    intro _raw_i14 _raw_i15 h_33098 h_33099 _
    let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_33098)
    have h_33098 : Litex.In _value_i14 (Litex.Q (M := M)) := h_33098
    let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_33099)
    have h_33099 : Litex.In _value_i15 (Litex.Q (M := M)) := h_33099
    change (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_33098) (Litex.rationalToComplex _value_i15 h_33099))
      exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_33098) (Litex.rationalToComplex _value_i15 h_33099))
      exact (Litex.mulInQ _value_i14 _value_i15 h_33098 h_33099))));
  let _wd_2_1 := _value_i17;
  let _wd_2_2 := _value_i18;
  (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_31355 h_31356 True.intro))
  let _object_w76 := (Litex.mul _value_i17 _value_i18 (Litex.rationalToComplex _value_i17 h_31355) (Litex.rationalToComplex _value_i18 h_31356))
  let _object_w77 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by
    intro _raw_i14 _raw_i15 h_34862 h_34863 _
    let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_34862)
    have h_34862 : Litex.In _value_i14 (Litex.Q (M := M)) := h_34862
    let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_34863)
    have h_34863 : Litex.In _value_i15 (Litex.Q (M := M)) := h_34863
    change (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_34862) (Litex.rationalToComplex _value_i15 h_34863))
      exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_34862) (Litex.rationalToComplex _value_i15 h_34863))
      exact (Litex.mulInQ _value_i14 _value_i15 h_34862 h_34863))));
  let _wd_2_1 := _object_w73;
  let _wd_2_2 := _value_i18;
  (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
    let _atomic_wd_1_0 := _object_w73
    exact (Litex.inOfSame _object_w73 _object_w73 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w73) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w73))) h_31356 True.intro))
  let _object_w78 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by
    intro _raw_i14 _raw_i15 h_35076 h_35077 _
    let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_35076)
    have h_35076 : Litex.In _value_i14 (Litex.Q (M := M)) := h_35076
    let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_35077)
    have h_35077 : Litex.In _value_i15 (Litex.Q (M := M)) := h_35077
    change (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_35076) (Litex.rationalToComplex _value_i15 h_35077))
      exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_35076) (Litex.rationalToComplex _value_i15 h_35077))
      exact (Litex.mulInQ _value_i14 _value_i15 h_35076 h_35077))));
  let _wd_2_1 := _object_w74;
  let _wd_2_2 := _value_i18;
  (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
    let _atomic_wd_1_0 := _object_w74
    exact (Litex.mulInQ _value_i16 _value_i17 h_31354 h_31355)) h_31356 True.intro))
  let _object_w79 := (let _wd_2_0 := _object_w74;
  let _wd_2_1 := _value_i18;
  (Litex.mul _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := _object_w74
    exact (Litex.mulInC _value_i16 _value_i17 (Litex.rationalToComplex _value_i16 h_31354) (Litex.rationalToComplex _value_i17 h_31355))) (Litex.rationalToComplex _wd_2_1 h_31356)))
  let _object_w80 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by
    intro _raw_i14 _raw_i15 h_36200 h_36201 _
    let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_36200)
    have h_36200 : Litex.In _value_i14 (Litex.Q (M := M)) := h_36200
    let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_36201)
    have h_36201 : Litex.In _value_i15 (Litex.Q (M := M)) := h_36201
    change (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_36200) (Litex.rationalToComplex _value_i15 h_36201))
      exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_36200) (Litex.rationalToComplex _value_i15 h_36201))
      exact (Litex.mulInQ _value_i14 _value_i15 h_36200 h_36201))));
  let _wd_2_1 := _value_i16;
  let _wd_2_2 := _object_w75;
  (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_31354 (by
    let _atomic_wd_1_0 := _object_w75
    exact (Litex.inOfSame _object_w75 _object_w75 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w75) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w75))) True.intro))
  let _object_w81 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by
    intro _raw_i14 _raw_i15 h_36410 h_36411 _
    let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_36410)
    have h_36410 : Litex.In _value_i14 (Litex.Q (M := M)) := h_36410
    let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_36411)
    have h_36411 : Litex.In _value_i15 (Litex.Q (M := M)) := h_36411
    change (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_36410) (Litex.rationalToComplex _value_i15 h_36411))
      exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_36410) (Litex.rationalToComplex _value_i15 h_36411))
      exact (Litex.mulInQ _value_i14 _value_i15 h_36410 h_36411))));
  let _wd_2_1 := _value_i16;
  let _wd_2_2 := _object_w76;
  (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_31354 (by
    let _atomic_wd_1_0 := _object_w76
    exact (Litex.mulInQ _value_i17 _value_i18 h_31355 h_31356)) True.intro))
  let _object_w82 := (let _wd_2_0 := _value_i16;
  let _wd_2_1 := _object_w76;
  (Litex.mul _wd_2_0 _wd_2_1 (Litex.rationalToComplex _wd_2_0 h_31354) (by
    let _atomic_wd_1_0 := _object_w76
    exact (Litex.mulInC _value_i17 _value_i18 (Litex.rationalToComplex _value_i17 h_31355) (Litex.rationalToComplex _value_i18 h_31356)))))
  exact (((by
    let _equal_wd_1_0 := _object_w73
    let _equal_wd_1_1 := _object_w74
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w75
    let _equal_wd_1_1 := _object_w76
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w77
    let _equal_wd_1_1 := _object_w78
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w78
    let _equal_wd_1_1 := _object_w79
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w80
    let _equal_wd_1_1 := _object_w81
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w81
    let _equal_wd_1_1 := _object_w82
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w79
    let _equal_wd_1_1 := _object_w82
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w77
    let _equal_wd_1_1 := _object_w80
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))))))))))))
) := (by
  intro _Host_i16 _rep_i16 _value_i16 h_31354 _Host_i17 _rep_i17 _value_i17 h_31355 _Host_i18 _rep_i18 _value_i18 h_31356
  let _object_w73 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by
    intro _raw_i14 _raw_i15 h_31370 h_31371 _
    let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_31370)
    have h_31370 : Litex.In _value_i14 (Litex.Q (M := M)) := h_31370
    let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_31371)
    have h_31371 : Litex.In _value_i15 (Litex.Q (M := M)) := h_31371
    change (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_31370) (Litex.rationalToComplex _value_i15 h_31371))
      exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_31370) (Litex.rationalToComplex _value_i15 h_31371))
      exact (Litex.mulInQ _value_i14 _value_i15 h_31370 h_31371))));
  let _wd_2_1 := _value_i16;
  let _wd_2_2 := _value_i17;
  (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_31354 h_31355 True.intro))
  let _object_w74 := (Litex.mul _value_i16 _value_i17 (Litex.rationalToComplex _value_i16 h_31354) (Litex.rationalToComplex _value_i17 h_31355))
  have h_31333 : (by
    let _equal_wd_1_0 := _object_w73
    let _equal_wd_1_1 := _object_w74
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i16), (Litex.denote _value_i17)])) = (M.mulValue (Litex.denote _value_i16) (Litex.denote _value_i17)) from by
            have _litex_residual : (M.mulValue (Litex.denote _value_i16) (Litex.denote _value_i17)) = (M.mulValue (Litex.denote _value_i16) (Litex.denote _value_i17)) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i16), (Litex.denote _value_i17)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i16), (Litex.denote _value_i17)])) = (M.mulValue (Litex.denote _value_i16) (Litex.denote _value_i17)) from by
            let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by
              intro _raw_i14 _raw_i15 h_32693 h_32694 _
              let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_32693)
              have h_32693 : Litex.In _value_i14 (Litex.Q (M := M)) := h_32693
              let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_32694)
              have h_32694 : Litex.In _value_i15 (Litex.Q (M := M)) := h_32694
              change (by
                let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_32693) (Litex.rationalToComplex _value_i15 h_32694))
                exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_32693) (Litex.rationalToComplex _value_i15 h_32694))
                exact (Litex.mulInQ _value_i14 _value_i15 h_32693 h_32694))));
            let _wd_2_1 := _value_i16;
            let _wd_2_2 := _value_i17;
            (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_31354 h_31355 True.intro))
            let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by
              intro _raw_i14 _raw_i15 h_32856 h_32857 _
              let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_32856)
              have h_32856 : Litex.In _value_i14 (Litex.Q (M := M)) := h_32856
              let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_32857)
              have h_32857 : Litex.In _value_i15 (Litex.Q (M := M)) := h_32857
              change (by
                let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_32856) (Litex.rationalToComplex _value_i15 h_32857))
                exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_32856) (Litex.rationalToComplex _value_i15 h_32857))
                exact (Litex.mulInQ _value_i14 _value_i15 h_32856 h_32857))));
            let _wd_2_1 := _value_i16;
            let _wd_2_2 := _value_i17;
            (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_31354 h_31355 True.intro))
            have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
            have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i16) (Litex.denote _value_i17)) from rfl))
          ))).trans _litex_residual)
        )
    )
  let _object_w75 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by
    intro _raw_i14 _raw_i15 h_33098 h_33099 _
    let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_33098)
    have h_33098 : Litex.In _value_i14 (Litex.Q (M := M)) := h_33098
    let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_33099)
    have h_33099 : Litex.In _value_i15 (Litex.Q (M := M)) := h_33099
    change (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_33098) (Litex.rationalToComplex _value_i15 h_33099))
      exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_33098) (Litex.rationalToComplex _value_i15 h_33099))
      exact (Litex.mulInQ _value_i14 _value_i15 h_33098 h_33099))));
  let _wd_2_1 := _value_i17;
  let _wd_2_2 := _value_i18;
  (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_31355 h_31356 True.intro))
  let _object_w76 := (Litex.mul _value_i17 _value_i18 (Litex.rationalToComplex _value_i17 h_31355) (Litex.rationalToComplex _value_i18 h_31356))
  have h_31334 : (by
    let _equal_wd_1_0 := _object_w75
    let _equal_wd_1_1 := _object_w76
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i17), (Litex.denote _value_i18)])) = (M.mulValue (Litex.denote _value_i17) (Litex.denote _value_i18)) from by
            have _litex_residual : (M.mulValue (Litex.denote _value_i17) (Litex.denote _value_i18)) = (M.mulValue (Litex.denote _value_i17) (Litex.denote _value_i18)) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i17), (Litex.denote _value_i18)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i17), (Litex.denote _value_i18)])) = (M.mulValue (Litex.denote _value_i17) (Litex.denote _value_i18)) from by
            let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by
              intro _raw_i14 _raw_i15 h_34449 h_34450 _
              let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_34449)
              have h_34449 : Litex.In _value_i14 (Litex.Q (M := M)) := h_34449
              let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_34450)
              have h_34450 : Litex.In _value_i15 (Litex.Q (M := M)) := h_34450
              change (by
                let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_34449) (Litex.rationalToComplex _value_i15 h_34450))
                exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_34449) (Litex.rationalToComplex _value_i15 h_34450))
                exact (Litex.mulInQ _value_i14 _value_i15 h_34449 h_34450))));
            let _wd_2_1 := _value_i17;
            let _wd_2_2 := _value_i18;
            (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_31355 h_31356 True.intro))
            let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by
              intro _raw_i14 _raw_i15 h_34616 h_34617 _
              let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_34616)
              have h_34616 : Litex.In _value_i14 (Litex.Q (M := M)) := h_34616
              let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_34617)
              have h_34617 : Litex.In _value_i15 (Litex.Q (M := M)) := h_34617
              change (by
                let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_34616) (Litex.rationalToComplex _value_i15 h_34617))
                exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
              exact (by
                let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_34616) (Litex.rationalToComplex _value_i15 h_34617))
                exact (Litex.mulInQ _value_i14 _value_i15 h_34616 h_34617))));
            let _wd_2_1 := _value_i17;
            let _wd_2_2 := _value_i18;
            (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_31355 h_31356 True.intro))
            have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
            have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i17) (Litex.denote _value_i18)) from rfl))
          ))).trans _litex_residual)
        )
    )
  let _object_w77 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by
    intro _raw_i14 _raw_i15 h_34862 h_34863 _
    let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_34862)
    have h_34862 : Litex.In _value_i14 (Litex.Q (M := M)) := h_34862
    let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_34863)
    have h_34863 : Litex.In _value_i15 (Litex.Q (M := M)) := h_34863
    change (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_34862) (Litex.rationalToComplex _value_i15 h_34863))
      exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_34862) (Litex.rationalToComplex _value_i15 h_34863))
      exact (Litex.mulInQ _value_i14 _value_i15 h_34862 h_34863))));
  let _wd_2_1 := _object_w73;
  let _wd_2_2 := _value_i18;
  (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
    let _atomic_wd_1_0 := _object_w73
    exact (Litex.inOfSame _object_w73 _object_w73 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w73) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w73))) h_31356 True.intro))
  let _object_w78 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by
    intro _raw_i14 _raw_i15 h_35076 h_35077 _
    let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_35076)
    have h_35076 : Litex.In _value_i14 (Litex.Q (M := M)) := h_35076
    let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_35077)
    have h_35077 : Litex.In _value_i15 (Litex.Q (M := M)) := h_35077
    change (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_35076) (Litex.rationalToComplex _value_i15 h_35077))
      exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_35076) (Litex.rationalToComplex _value_i15 h_35077))
      exact (Litex.mulInQ _value_i14 _value_i15 h_35076 h_35077))));
  let _wd_2_1 := _object_w74;
  let _wd_2_2 := _value_i18;
  (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
    let _atomic_wd_1_0 := _object_w74
    exact (Litex.mulInQ _value_i16 _value_i17 h_31354 h_31355)) h_31356 True.intro))
  have h_31335 : (by
    let _equal_wd_1_0 := _object_w77
    let _equal_wd_1_1 := _object_w78
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) h_31333 (show @Eq M.Value _ _ from Eq.refl _)))
        )
    )
  let _object_w79 := (let _wd_2_0 := _object_w74;
  let _wd_2_1 := _value_i18;
  (Litex.mul _wd_2_0 _wd_2_1 (by
    let _atomic_wd_1_0 := _object_w74
    exact (Litex.mulInC _value_i16 _value_i17 (Litex.rationalToComplex _value_i16 h_31354) (Litex.rationalToComplex _value_i17 h_31355))) (Litex.rationalToComplex _wd_2_1 h_31356)))
  have h_31336 : (by
    let _equal_wd_1_0 := _object_w78
    let _equal_wd_1_1 := _object_w79
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.mulValue (Litex.denote _value_i16) (Litex.denote _value_i17)), (Litex.denote _value_i18)])) = (M.mulValue (M.mulValue (Litex.denote _value_i16) (Litex.denote _value_i17)) (Litex.denote _value_i18)) from by
            have _litex_residual : (M.mulValue (M.mulValue (Litex.denote _value_i16) (Litex.denote _value_i17)) (Litex.denote _value_i18)) = (M.mulValue (M.mulValue (Litex.denote _value_i16) (Litex.denote _value_i17)) (Litex.denote _value_i18)) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.mulValue (Litex.denote _value_i16) (Litex.denote _value_i17)), (Litex.denote _value_i18)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.mulValue (Litex.denote _value_i16) (Litex.denote _value_i17)), (Litex.denote _value_i18)])) = (M.mulValue (M.mulValue (Litex.denote _value_i16) (Litex.denote _value_i17)) (Litex.denote _value_i18)) from by
            let _litex_original := _object_w78
            let _litex_literal := _object_w78
            have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
            have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (M.mulValue (Litex.denote _value_i16) (Litex.denote _value_i17)) (Litex.denote _value_i18)) from rfl))
          ))).trans _litex_residual)
        )
    )
  let _object_w80 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by
    intro _raw_i14 _raw_i15 h_36200 h_36201 _
    let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_36200)
    have h_36200 : Litex.In _value_i14 (Litex.Q (M := M)) := h_36200
    let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_36201)
    have h_36201 : Litex.In _value_i15 (Litex.Q (M := M)) := h_36201
    change (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_36200) (Litex.rationalToComplex _value_i15 h_36201))
      exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_36200) (Litex.rationalToComplex _value_i15 h_36201))
      exact (Litex.mulInQ _value_i14 _value_i15 h_36200 h_36201))));
  let _wd_2_1 := _value_i16;
  let _wd_2_2 := _object_w75;
  (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_31354 (by
    let _atomic_wd_1_0 := _object_w75
    exact (Litex.inOfSame _object_w75 _object_w75 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w75) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w75))) True.intro))
  let _object_w81 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by
    intro _raw_i14 _raw_i15 h_36410 h_36411 _
    let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_36410)
    have h_36410 : Litex.In _value_i14 (Litex.Q (M := M)) := h_36410
    let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_36411)
    have h_36411 : Litex.In _value_i15 (Litex.Q (M := M)) := h_36411
    change (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_36410) (Litex.rationalToComplex _value_i15 h_36411))
      exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.mul _value_i14 _value_i15 (Litex.rationalToComplex _value_i14 h_36410) (Litex.rationalToComplex _value_i15 h_36411))
      exact (Litex.mulInQ _value_i14 _value_i15 h_36410 h_36411))));
  let _wd_2_1 := _value_i16;
  let _wd_2_2 := _object_w76;
  (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_31354 (by
    let _atomic_wd_1_0 := _object_w76
    exact (Litex.mulInQ _value_i17 _value_i18 h_31355 h_31356)) True.intro))
  have h_31337 : (by
    let _equal_wd_1_0 := _object_w80
    let _equal_wd_1_1 := _object_w81
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_31334))
        )
    )
  let _object_w82 := (let _wd_2_0 := _value_i16;
  let _wd_2_1 := _object_w76;
  (Litex.mul _wd_2_0 _wd_2_1 (Litex.rationalToComplex _wd_2_0 h_31354) (by
    let _atomic_wd_1_0 := _object_w76
    exact (Litex.mulInC _value_i17 _value_i18 (Litex.rationalToComplex _value_i17 h_31355) (Litex.rationalToComplex _value_i18 h_31356)))))
  have h_31338 : (by
    let _equal_wd_1_0 := _object_w81
    let _equal_wd_1_1 := _object_w82
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i16), (M.mulValue (Litex.denote _value_i17) (Litex.denote _value_i18))])) = (M.mulValue (Litex.denote _value_i16) (M.mulValue (Litex.denote _value_i17) (Litex.denote _value_i18))) from by
            have _litex_residual : (M.mulValue (Litex.denote _value_i16) (M.mulValue (Litex.denote _value_i17) (Litex.denote _value_i18))) = (M.mulValue (Litex.denote _value_i16) (M.mulValue (Litex.denote _value_i17) (Litex.denote _value_i18))) := (show @Eq M.Value _ _ from Eq.refl _)
            exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i16), (M.mulValue (Litex.denote _value_i17) (Litex.denote _value_i18))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i16), (M.mulValue (Litex.denote _value_i17) (Litex.denote _value_i18))])) = (M.mulValue (Litex.denote _value_i16) (M.mulValue (Litex.denote _value_i17) (Litex.denote _value_i18))) from by
            let _litex_original := _object_w81
            let _litex_literal := _object_w81
            have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
            have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
            exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (M.mulValue _raw_i14 _raw_i15)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i16) (M.mulValue (Litex.denote _value_i17) (Litex.denote _value_i18))) from rfl))
          ))).trans _litex_residual)
        )
    )
  have h_31339 : (by
    let _equal_wd_1_0 := _object_w79
    let _equal_wd_1_1 := _object_w82
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i16 (Litex.rationalToComplex _value_i16 h_31354)) * (Litex.NativeBridge.asComplex _value_i17 (Litex.rationalToComplex _value_i17 h_31355))) * (Litex.NativeBridge.asComplex _value_i18 (Litex.rationalToComplex _value_i18 h_31356))) ((Litex.NativeBridge.asComplex _value_i16 (Litex.rationalToComplex _value_i16 h_31354)) * ((Litex.NativeBridge.asComplex _value_i17 (Litex.rationalToComplex _value_i17 h_31355)) * (Litex.NativeBridge.asComplex _value_i18 (Litex.rationalToComplex _value_i18 h_31356)))) (Litex.NativeBridge.denoteMul (_object_w79).val.left _value_i18 (_object_w79).wd.1 (_object_w79).wd.2 _ _ (Litex.NativeBridge.denoteMul _value_i16 _value_i17 (_object_w74).wd.1 (_object_w74).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i16 (Litex.rationalToComplex _value_i16 h_31354)) (Litex.NativeBridge.asComplex_spec _value_i17 (Litex.rationalToComplex _value_i17 h_31355))) (Litex.NativeBridge.asComplex_spec _value_i18 (Litex.rationalToComplex _value_i18 h_31356))) (Litex.NativeBridge.denoteMul _value_i16 (_object_w82).val.right (_object_w82).wd.1 (_object_w82).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i16 (Litex.rationalToComplex _value_i16 h_31354)) (Litex.NativeBridge.denoteMul _value_i17 _value_i18 (_object_w76).wd.1 (_object_w76).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i17 (Litex.rationalToComplex _value_i17 h_31355)) (Litex.NativeBridge.asComplex_spec _value_i18 (Litex.rationalToComplex _value_i18 h_31356)))) (by ring!))
        )
    )
  have h_31340 : (by
    let _equal_wd_1_0 := _object_w77
    let _equal_wd_1_1 := _object_w80
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
    (by
      litex_checked_step =>
        exact (
          ((((((((h_31335).trans h_31336)).trans h_31339)).trans (h_31338).symm)).trans (h_31337).symm)
        )
    )
  exact (And.intro h_31333 (And.intro h_31334 (And.intro h_31335 (And.intro h_31336 (And.intro h_31337 (And.intro h_31338 (And.intro h_31339 h_31340)))))))
);
let h_37524 : (by
  let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  (let _setElement_0 := _wd_2_0;
    let _setElement_1 := _wd_2_1;
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
      let _atomic_wd_2_0 := _wd_2_0
      let _atomic_wd_2_1 := _wd_2_1
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0))
  exact Litex.Subset _atomic_wd_1_0 (Litex.Q (M := M))) := (by
  let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
  (let _setElement_0 := _wd_2_0;
    let _setElement_1 := _wd_2_1;
    let _setTail_2 := Litex.emptySet (M := M);
    let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
    let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
    let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
      let _atomic_wd_2_0 := _wd_2_0
      let _atomic_wd_2_1 := _wd_2_1
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
    let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
    _setTail_0))
  exact (by
    let _set := _atomic_wd_1_0
    exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Q (M := M)) _set.wd (by
    let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℚ) / (2 : ℚ)) (by norm_num)))) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Q (M := M)) _set.val.tail.wd (by
    let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)) _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℚ) / (3 : ℚ)) (by norm_num)))) (Litex.emptySubset (Litex.Q (M := M)))))));
Litex.finiteFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i13 : M.Value) => True)) h_28348 (Litex.formulaFnInFnSet _wd_1_1) (Litex.formulaFnInFnSet _wd_1_2) h_28356 (fun i hi => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.rational) (Litex.denote (Litex.Q (M := M))) (M.standard_isSet Litex.StandardSetValue.rational) (Litex.isSet (Litex.Q (M := M))) (fun (_raw_i13 : M.Value) => True) i).mpr ⟨h_37524 i hi, True.intro⟩) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x1 _fold_h1 => (And.right (And.right (And.right (h_28361 _fold_x0 _fold_h0 _fold_x1 _fold_h1)))))))) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x2 _fold_h2 => (And.right (And.right (And.right (And.right (And.right (And.right (And.right (h_31341 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2))))))))))))))))

theorem h_28229 : (by
  let _equal_wd_1_0 := (_object_w104 (M := M))
  let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w104 (M := M));
        let _equal_wd_1_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (Eq.trans (Eq.symm (by
          let _left := (let _wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
        (let _setElement_0 := _wd_2_0;
          let _setElement_1 := _wd_2_1;
          let _setTail_2 := Litex.emptySet (M := M);
          let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
          let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
          let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
            let _atomic_wd_1_0 := _wd_2_0
            let _atomic_wd_1_1 := _wd_2_1
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 _atomic_wd_1_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2.1 (_atomic_wd_1_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_1_1).wd.1 (_atomic_wd_1_1).wd.2.1 (_atomic_wd_1_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
          let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
          _setTail_0));
        let _wd_1_1 := (Litex.formulaFn (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
          intro _raw_i1 h_18924 _
          let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_18924)
          have h_18924 : Litex.In _value_i1 (Litex.Q (M := M)) := h_18924
          change Litex.In _value_i1 (Litex.Q (M := M))
          exact h_18924));
        let _wd_1_2 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
          intro _raw_i2 _raw_i3 h_18943 h_18944 _
          let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_18943)
          have h_18943 : Litex.In _value_i2 (Litex.Q (M := M)) := h_18943
          let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_18944)
          have h_18944 : Litex.In _value_i3 (Litex.Q (M := M)) := h_18944
          change (by
            let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_18943) (Litex.rationalToComplex _value_i3 h_18944))
            exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
          exact (by
            let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_18943) (Litex.rationalToComplex _value_i3 h_18944))
            exact (Litex.mulInQ _value_i2 _value_i3 h_18943 h_18944))));
        let _wd_1_3 := (Litex.number (M := M) (2 : ℂ));
        (let h_19022 : (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact Litex.IsFiniteSet _atomic_wd_1_0) := (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact (let _finite_tail_0 := _atomic_wd_1_0;
          let _finite_tail_1 := _finite_tail_0.val.tail;
          let _finite_tail_2 := _finite_tail_1.val.tail;
          have _finite_2 : Litex.IsFiniteSet _finite_tail_2 := Litex.finiteSetEmpty;
          have _finite_1 := Litex.finiteSetInsert _finite_tail_1 _finite_2;
          have _finite_0 := Litex.finiteSetInsert _finite_tail_0 _finite_1;
          _finite_0));
        let h_19036 : Litex.In _wd_1_3 (Litex.Q (M := M)) := (Litex.NativeBridge.numberInQOfEq (M := M) (2 : ℂ) (2 : ℚ) (by norm_num));
        let h_19041 : ∀ {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_19054 : Litex.In _value_i10 (Litex.Q (M := M))) {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_19055 : Litex.In _value_i11 (Litex.Q (M := M))), (by
          let _object_w48 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_19069 h_19070 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_19069)
            have h_19069 : Litex.In _value_i2 (Litex.Q (M := M)) := h_19069
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_19070)
            have h_19070 : Litex.In _value_i3 (Litex.Q (M := M)) := h_19070
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_19069) (Litex.rationalToComplex _value_i3 h_19070))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_19069) (Litex.rationalToComplex _value_i3 h_19070))
              exact (Litex.mulInQ _value_i2 _value_i3 h_19069 h_19070))));
          let _wd_2_1 := _value_i10;
          let _wd_2_2 := _value_i11;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_19054 h_19055 True.intro))
          let _object_w49 := (Litex.mul _value_i10 _value_i11 (Litex.rationalToComplex _value_i10 h_19054) (Litex.rationalToComplex _value_i11 h_19055))
          let _object_w50 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_20545 h_20546 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_20545)
            have h_20545 : Litex.In _value_i2 (Litex.Q (M := M)) := h_20545
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_20546)
            have h_20546 : Litex.In _value_i3 (Litex.Q (M := M)) := h_20546
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_20545) (Litex.rationalToComplex _value_i3 h_20546))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_20545) (Litex.rationalToComplex _value_i3 h_20546))
              exact (Litex.mulInQ _value_i2 _value_i3 h_20545 h_20546))));
          let _wd_2_1 := _value_i11;
          let _wd_2_2 := _value_i10;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_19055 h_19054 True.intro))
          let _object_w51 := (Litex.mul _value_i11 _value_i10 (Litex.rationalToComplex _value_i11 h_19055) (Litex.rationalToComplex _value_i10 h_19054))
          exact (((by
            let _equal_wd_2_0 := _object_w48
            let _equal_wd_2_1 := _object_w49
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
            let _equal_wd_2_0 := _object_w50
            let _equal_wd_2_1 := _object_w51
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
            let _equal_wd_2_0 := _object_w49
            let _equal_wd_2_1 := _object_w51
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((by
            let _equal_wd_2_0 := _object_w48
            let _equal_wd_2_1 := _object_w50
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)))))))
        ) := (by
          intro _Host_i10 _rep_i10 _value_i10 h_19054 _Host_i11 _rep_i11 _value_i11 h_19055
          let _object_w48 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_19069 h_19070 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_19069)
            have h_19069 : Litex.In _value_i2 (Litex.Q (M := M)) := h_19069
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_19070)
            have h_19070 : Litex.In _value_i3 (Litex.Q (M := M)) := h_19070
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_19069) (Litex.rationalToComplex _value_i3 h_19070))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_19069) (Litex.rationalToComplex _value_i3 h_19070))
              exact (Litex.mulInQ _value_i2 _value_i3 h_19069 h_19070))));
          let _wd_2_1 := _value_i10;
          let _wd_2_2 := _value_i11;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_19054 h_19055 True.intro))
          let _object_w49 := (Litex.mul _value_i10 _value_i11 (Litex.rationalToComplex _value_i10 h_19054) (Litex.rationalToComplex _value_i11 h_19055))
          have h_19037 : (by
            let _equal_wd_2_0 := _object_w48
            let _equal_wd_2_1 := _object_w49
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])) = (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) from by
                    have _litex_residual : (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) = (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])) = (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) from by
                    let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_20196 h_20197 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_20196)
                      have h_20196 : Litex.In _value_i2 (Litex.Q (M := M)) := h_20196
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_20197)
                      have h_20197 : Litex.In _value_i3 (Litex.Q (M := M)) := h_20197
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_20196) (Litex.rationalToComplex _value_i3 h_20197))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_20196) (Litex.rationalToComplex _value_i3 h_20197))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_20196 h_20197))));
                    let _wd_2_1 := _value_i10;
                    let _wd_2_2 := _value_i11;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_19054 h_19055 True.intro))
                    let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_20339 h_20340 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_20339)
                      have h_20339 : Litex.In _value_i2 (Litex.Q (M := M)) := h_20339
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_20340)
                      have h_20340 : Litex.In _value_i3 (Litex.Q (M := M)) := h_20340
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_20339) (Litex.rationalToComplex _value_i3 h_20340))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_20339) (Litex.rationalToComplex _value_i3 h_20340))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_20339 h_20340))));
                    let _wd_2_1 := _value_i10;
                    let _wd_2_2 := _value_i11;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_19054 h_19055 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          let _object_w50 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_20545 h_20546 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_20545)
            have h_20545 : Litex.In _value_i2 (Litex.Q (M := M)) := h_20545
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_20546)
            have h_20546 : Litex.In _value_i3 (Litex.Q (M := M)) := h_20546
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_20545) (Litex.rationalToComplex _value_i3 h_20546))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_20545) (Litex.rationalToComplex _value_i3 h_20546))
              exact (Litex.mulInQ _value_i2 _value_i3 h_20545 h_20546))));
          let _wd_2_1 := _value_i11;
          let _wd_2_2 := _value_i10;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_19055 h_19054 True.intro))
          let _object_w51 := (Litex.mul _value_i11 _value_i10 (Litex.rationalToComplex _value_i11 h_19055) (Litex.rationalToComplex _value_i10 h_19054))
          have h_19038 : (by
            let _equal_wd_2_0 := _object_w50
            let _equal_wd_2_1 := _object_w51
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i11), (Litex.denote _value_i10)])) = (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i10)) from by
                    have _litex_residual : (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i10)) = (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i10)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i11), (Litex.denote _value_i10)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i11), (Litex.denote _value_i10)])) = (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i10)) from by
                    let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_21672 h_21673 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_21672)
                      have h_21672 : Litex.In _value_i2 (Litex.Q (M := M)) := h_21672
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_21673)
                      have h_21673 : Litex.In _value_i3 (Litex.Q (M := M)) := h_21673
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_21672) (Litex.rationalToComplex _value_i3 h_21673))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_21672) (Litex.rationalToComplex _value_i3 h_21673))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_21672 h_21673))));
                    let _wd_2_1 := _value_i11;
                    let _wd_2_2 := _value_i10;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_19055 h_19054 True.intro))
                    let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_21815 h_21816 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_21815)
                      have h_21815 : Litex.In _value_i2 (Litex.Q (M := M)) := h_21815
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_21816)
                      have h_21816 : Litex.In _value_i3 (Litex.Q (M := M)) := h_21816
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_21815) (Litex.rationalToComplex _value_i3 h_21816))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_21815) (Litex.rationalToComplex _value_i3 h_21816))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_21815 h_21816))));
                    let _wd_2_1 := _value_i11;
                    let _wd_2_2 := _value_i10;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_19055 h_19054 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i10)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          have h_19039 : (by
            let _equal_wd_2_0 := _object_w49
            let _equal_wd_2_1 := _object_w51
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.sameOfDenoteNumber _ _ ((Litex.NativeBridge.asComplex _value_i10 (Litex.rationalToComplex _value_i10 h_19054)) * (Litex.NativeBridge.asComplex _value_i11 (Litex.rationalToComplex _value_i11 h_19055))) ((Litex.NativeBridge.asComplex _value_i11 (Litex.rationalToComplex _value_i11 h_19055)) * (Litex.NativeBridge.asComplex _value_i10 (Litex.rationalToComplex _value_i10 h_19054))) (Litex.NativeBridge.denoteMul _value_i10 _value_i11 (_object_w49).wd.1 (_object_w49).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.rationalToComplex _value_i10 h_19054)) (Litex.NativeBridge.asComplex_spec _value_i11 (Litex.rationalToComplex _value_i11 h_19055))) (Litex.NativeBridge.denoteMul _value_i11 _value_i10 (_object_w51).wd.1 (_object_w51).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i11 (Litex.rationalToComplex _value_i11 h_19055)) (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.rationalToComplex _value_i10 h_19054))) (by ring!))
                )
            )
          have h_19040 : (by
            let _equal_wd_2_0 := _object_w48
            let _equal_wd_2_1 := _object_w50
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  ((((h_19037).trans h_19039)).trans (h_19038).symm)
                )
            )
          exact (And.intro h_19037 (And.intro h_19038 (And.intro h_19039 h_19040)))
        );
        let h_22021 : ∀ {_Host_i10 : Type _} [_rep_i10 : Litex.Representation M _Host_i10] (_value_i10 : Litex.Obj (M := M) _Host_i10) (h_22034 : Litex.In _value_i10 (Litex.Q (M := M))) {_Host_i11 : Type _} [_rep_i11 : Litex.Representation M _Host_i11] (_value_i11 : Litex.Obj (M := M) _Host_i11) (h_22035 : Litex.In _value_i11 (Litex.Q (M := M))) {_Host_i12 : Type _} [_rep_i12 : Litex.Representation M _Host_i12] (_value_i12 : Litex.Obj (M := M) _Host_i12) (h_22036 : Litex.In _value_i12 (Litex.Q (M := M))), (by
          let _object_w53 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_22050 h_22051 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_22050)
            have h_22050 : Litex.In _value_i2 (Litex.Q (M := M)) := h_22050
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_22051)
            have h_22051 : Litex.In _value_i3 (Litex.Q (M := M)) := h_22051
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_22050) (Litex.rationalToComplex _value_i3 h_22051))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_22050) (Litex.rationalToComplex _value_i3 h_22051))
              exact (Litex.mulInQ _value_i2 _value_i3 h_22050 h_22051))));
          let _wd_2_1 := _value_i10;
          let _wd_2_2 := _value_i11;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22034 h_22035 True.intro))
          let _object_w54 := (Litex.mul _value_i10 _value_i11 (Litex.rationalToComplex _value_i10 h_22034) (Litex.rationalToComplex _value_i11 h_22035))
          let _object_w55 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_23778 h_23779 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_23778)
            have h_23778 : Litex.In _value_i2 (Litex.Q (M := M)) := h_23778
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_23779)
            have h_23779 : Litex.In _value_i3 (Litex.Q (M := M)) := h_23779
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_23778) (Litex.rationalToComplex _value_i3 h_23779))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_23778) (Litex.rationalToComplex _value_i3 h_23779))
              exact (Litex.mulInQ _value_i2 _value_i3 h_23778 h_23779))));
          let _wd_2_1 := _value_i11;
          let _wd_2_2 := _value_i12;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22035 h_22036 True.intro))
          let _object_w56 := (Litex.mul _value_i11 _value_i12 (Litex.rationalToComplex _value_i11 h_22035) (Litex.rationalToComplex _value_i12 h_22036))
          let _object_w57 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_25542 h_25543 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_25542)
            have h_25542 : Litex.In _value_i2 (Litex.Q (M := M)) := h_25542
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_25543)
            have h_25543 : Litex.In _value_i3 (Litex.Q (M := M)) := h_25543
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25542) (Litex.rationalToComplex _value_i3 h_25543))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25542) (Litex.rationalToComplex _value_i3 h_25543))
              exact (Litex.mulInQ _value_i2 _value_i3 h_25542 h_25543))));
          let _wd_2_1 := _object_w53;
          let _wd_2_2 := _value_i12;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
            let _atomic_wd_1_0 := _object_w53
            exact (Litex.inOfSame _object_w53 _object_w53 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w53) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w53))) h_22036 True.intro))
          let _object_w58 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_25756 h_25757 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_25756)
            have h_25756 : Litex.In _value_i2 (Litex.Q (M := M)) := h_25756
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_25757)
            have h_25757 : Litex.In _value_i3 (Litex.Q (M := M)) := h_25757
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25756) (Litex.rationalToComplex _value_i3 h_25757))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25756) (Litex.rationalToComplex _value_i3 h_25757))
              exact (Litex.mulInQ _value_i2 _value_i3 h_25756 h_25757))));
          let _wd_2_1 := _object_w54;
          let _wd_2_2 := _value_i12;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
            let _atomic_wd_1_0 := _object_w54
            exact (Litex.mulInQ _value_i10 _value_i11 h_22034 h_22035)) h_22036 True.intro))
          let _object_w59 := (let _wd_2_0 := _object_w54;
          let _wd_2_1 := _value_i12;
          (Litex.mul _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _object_w54
            exact (Litex.mulInC _value_i10 _value_i11 (Litex.rationalToComplex _value_i10 h_22034) (Litex.rationalToComplex _value_i11 h_22035))) (Litex.rationalToComplex _wd_2_1 h_22036)))
          let _object_w60 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_26880 h_26881 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_26880)
            have h_26880 : Litex.In _value_i2 (Litex.Q (M := M)) := h_26880
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_26881)
            have h_26881 : Litex.In _value_i3 (Litex.Q (M := M)) := h_26881
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_26880) (Litex.rationalToComplex _value_i3 h_26881))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_26880) (Litex.rationalToComplex _value_i3 h_26881))
              exact (Litex.mulInQ _value_i2 _value_i3 h_26880 h_26881))));
          let _wd_2_1 := _value_i10;
          let _wd_2_2 := _object_w55;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22034 (by
            let _atomic_wd_1_0 := _object_w55
            exact (Litex.inOfSame _object_w55 _object_w55 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w55) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w55))) True.intro))
          let _object_w61 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_27090 h_27091 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_27090)
            have h_27090 : Litex.In _value_i2 (Litex.Q (M := M)) := h_27090
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_27091)
            have h_27091 : Litex.In _value_i3 (Litex.Q (M := M)) := h_27091
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_27090) (Litex.rationalToComplex _value_i3 h_27091))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_27090) (Litex.rationalToComplex _value_i3 h_27091))
              exact (Litex.mulInQ _value_i2 _value_i3 h_27090 h_27091))));
          let _wd_2_1 := _value_i10;
          let _wd_2_2 := _object_w56;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22034 (by
            let _atomic_wd_1_0 := _object_w56
            exact (Litex.mulInQ _value_i11 _value_i12 h_22035 h_22036)) True.intro))
          let _object_w62 := (let _wd_2_0 := _value_i10;
          let _wd_2_1 := _object_w56;
          (Litex.mul _wd_2_0 _wd_2_1 (Litex.rationalToComplex _wd_2_0 h_22034) (by
            let _atomic_wd_1_0 := _object_w56
            exact (Litex.mulInC _value_i11 _value_i12 (Litex.rationalToComplex _value_i11 h_22035) (Litex.rationalToComplex _value_i12 h_22036)))))
          exact (((by
            let _equal_wd_2_0 := _object_w53
            let _equal_wd_2_1 := _object_w54
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
            let _equal_wd_2_0 := _object_w55
            let _equal_wd_2_1 := _object_w56
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
            let _equal_wd_2_0 := _object_w57
            let _equal_wd_2_1 := _object_w58
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
            let _equal_wd_2_0 := _object_w58
            let _equal_wd_2_1 := _object_w59
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
            let _equal_wd_2_0 := _object_w60
            let _equal_wd_2_1 := _object_w61
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
            let _equal_wd_2_0 := _object_w61
            let _equal_wd_2_1 := _object_w62
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((((by
            let _equal_wd_2_0 := _object_w59
            let _equal_wd_2_1 := _object_w62
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)) ∧ ((by
            let _equal_wd_2_0 := _object_w57
            let _equal_wd_2_1 := _object_w60
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1)))))))))))))))
        ) := (by
          intro _Host_i10 _rep_i10 _value_i10 h_22034 _Host_i11 _rep_i11 _value_i11 h_22035 _Host_i12 _rep_i12 _value_i12 h_22036
          let _object_w53 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_22050 h_22051 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_22050)
            have h_22050 : Litex.In _value_i2 (Litex.Q (M := M)) := h_22050
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_22051)
            have h_22051 : Litex.In _value_i3 (Litex.Q (M := M)) := h_22051
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_22050) (Litex.rationalToComplex _value_i3 h_22051))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_22050) (Litex.rationalToComplex _value_i3 h_22051))
              exact (Litex.mulInQ _value_i2 _value_i3 h_22050 h_22051))));
          let _wd_2_1 := _value_i10;
          let _wd_2_2 := _value_i11;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22034 h_22035 True.intro))
          let _object_w54 := (Litex.mul _value_i10 _value_i11 (Litex.rationalToComplex _value_i10 h_22034) (Litex.rationalToComplex _value_i11 h_22035))
          have h_22013 : (by
            let _equal_wd_2_0 := _object_w53
            let _equal_wd_2_1 := _object_w54
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])) = (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) from by
                    have _litex_residual : (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) = (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (Litex.denote _value_i11)])) = (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) from by
                    let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_23373 h_23374 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_23373)
                      have h_23373 : Litex.In _value_i2 (Litex.Q (M := M)) := h_23373
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_23374)
                      have h_23374 : Litex.In _value_i3 (Litex.Q (M := M)) := h_23374
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_23373) (Litex.rationalToComplex _value_i3 h_23374))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_23373) (Litex.rationalToComplex _value_i3 h_23374))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_23373 h_23374))));
                    let _wd_2_1 := _value_i10;
                    let _wd_2_2 := _value_i11;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22034 h_22035 True.intro))
                    let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_23536 h_23537 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_23536)
                      have h_23536 : Litex.In _value_i2 (Litex.Q (M := M)) := h_23536
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_23537)
                      have h_23537 : Litex.In _value_i3 (Litex.Q (M := M)) := h_23537
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_23536) (Litex.rationalToComplex _value_i3 h_23537))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_23536) (Litex.rationalToComplex _value_i3 h_23537))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_23536 h_23537))));
                    let _wd_2_1 := _value_i10;
                    let _wd_2_2 := _value_i11;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22034 h_22035 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          let _object_w55 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_23778 h_23779 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_23778)
            have h_23778 : Litex.In _value_i2 (Litex.Q (M := M)) := h_23778
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_23779)
            have h_23779 : Litex.In _value_i3 (Litex.Q (M := M)) := h_23779
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_23778) (Litex.rationalToComplex _value_i3 h_23779))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_23778) (Litex.rationalToComplex _value_i3 h_23779))
              exact (Litex.mulInQ _value_i2 _value_i3 h_23778 h_23779))));
          let _wd_2_1 := _value_i11;
          let _wd_2_2 := _value_i12;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22035 h_22036 True.intro))
          let _object_w56 := (Litex.mul _value_i11 _value_i12 (Litex.rationalToComplex _value_i11 h_22035) (Litex.rationalToComplex _value_i12 h_22036))
          have h_22014 : (by
            let _equal_wd_2_0 := _object_w55
            let _equal_wd_2_1 := _object_w56
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i11), (Litex.denote _value_i12)])) = (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12)) from by
                    have _litex_residual : (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12)) = (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i11), (Litex.denote _value_i12)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i11), (Litex.denote _value_i12)])) = (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12)) from by
                    let _litex_original := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_25129 h_25130 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_25129)
                      have h_25129 : Litex.In _value_i2 (Litex.Q (M := M)) := h_25129
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_25130)
                      have h_25130 : Litex.In _value_i3 (Litex.Q (M := M)) := h_25130
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25129) (Litex.rationalToComplex _value_i3 h_25130))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25129) (Litex.rationalToComplex _value_i3 h_25130))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_25129 h_25130))));
                    let _wd_2_1 := _value_i11;
                    let _wd_2_2 := _value_i12;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22035 h_22036 True.intro))
                    let _litex_literal := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
                      intro _raw_i2 _raw_i3 h_25296 h_25297 _
                      let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_25296)
                      have h_25296 : Litex.In _value_i2 (Litex.Q (M := M)) := h_25296
                      let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_25297)
                      have h_25297 : Litex.In _value_i3 (Litex.Q (M := M)) := h_25297
                      change (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25296) (Litex.rationalToComplex _value_i3 h_25297))
                        exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
                      exact (by
                        let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25296) (Litex.rationalToComplex _value_i3 h_25297))
                        exact (Litex.mulInQ _value_i2 _value_i3 h_25296 h_25297))));
                    let _wd_2_1 := _value_i11;
                    let _wd_2_2 := _value_i12;
                    (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22035 h_22036 True.intro))
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          let _object_w57 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_25542 h_25543 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_25542)
            have h_25542 : Litex.In _value_i2 (Litex.Q (M := M)) := h_25542
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_25543)
            have h_25543 : Litex.In _value_i3 (Litex.Q (M := M)) := h_25543
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25542) (Litex.rationalToComplex _value_i3 h_25543))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25542) (Litex.rationalToComplex _value_i3 h_25543))
              exact (Litex.mulInQ _value_i2 _value_i3 h_25542 h_25543))));
          let _wd_2_1 := _object_w53;
          let _wd_2_2 := _value_i12;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
            let _atomic_wd_1_0 := _object_w53
            exact (Litex.inOfSame _object_w53 _object_w53 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w53) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w53))) h_22036 True.intro))
          let _object_w58 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_25756 h_25757 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_25756)
            have h_25756 : Litex.In _value_i2 (Litex.Q (M := M)) := h_25756
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_25757)
            have h_25757 : Litex.In _value_i3 (Litex.Q (M := M)) := h_25757
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25756) (Litex.rationalToComplex _value_i3 h_25757))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_25756) (Litex.rationalToComplex _value_i3 h_25757))
              exact (Litex.mulInQ _value_i2 _value_i3 h_25756 h_25757))));
          let _wd_2_1 := _object_w54;
          let _wd_2_2 := _value_i12;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) (by
            let _atomic_wd_1_0 := _object_w54
            exact (Litex.mulInQ _value_i10 _value_i11 h_22034 h_22035)) h_22036 True.intro))
          have h_22015 : (by
            let _equal_wd_2_0 := _object_w57
            let _equal_wd_2_1 := _object_w58
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) h_22013 (show @Eq M.Value _ _ from Eq.refl _)))
                )
            )
          let _object_w59 := (let _wd_2_0 := _object_w54;
          let _wd_2_1 := _value_i12;
          (Litex.mul _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _object_w54
            exact (Litex.mulInC _value_i10 _value_i11 (Litex.rationalToComplex _value_i10 h_22034) (Litex.rationalToComplex _value_i11 h_22035))) (Litex.rationalToComplex _wd_2_1 h_22036)))
          have h_22016 : (by
            let _equal_wd_2_0 := _object_w58
            let _equal_wd_2_1 := _object_w59
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)), (Litex.denote _value_i12)])) = (M.mulValue (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) (Litex.denote _value_i12)) from by
                    have _litex_residual : (M.mulValue (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) (Litex.denote _value_i12)) = (M.mulValue (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) (Litex.denote _value_i12)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)), (Litex.denote _value_i12)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)), (Litex.denote _value_i12)])) = (M.mulValue (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) (Litex.denote _value_i12)) from by
                    let _litex_original := _object_w58
                    let _litex_literal := _object_w58
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (M.mulValue (Litex.denote _value_i10) (Litex.denote _value_i11)) (Litex.denote _value_i12)) from rfl))
                  ))).trans _litex_residual)
                )
            )
          let _object_w60 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_26880 h_26881 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_26880)
            have h_26880 : Litex.In _value_i2 (Litex.Q (M := M)) := h_26880
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_26881)
            have h_26881 : Litex.In _value_i3 (Litex.Q (M := M)) := h_26881
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_26880) (Litex.rationalToComplex _value_i3 h_26881))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_26880) (Litex.rationalToComplex _value_i3 h_26881))
              exact (Litex.mulInQ _value_i2 _value_i3 h_26880 h_26881))));
          let _wd_2_1 := _value_i10;
          let _wd_2_2 := _object_w55;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22034 (by
            let _atomic_wd_1_0 := _object_w55
            exact (Litex.inOfSame _object_w55 _object_w55 (Litex.Q (M := M)) (Litex.Q (M := M)) (Litex.sameRefl _object_w55) (Litex.sameRefl (Litex.Q (M := M))) (Litex.call2InOutput _object_w55))) True.intro))
          let _object_w61 := (let _wd_2_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_27090 h_27091 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_27090)
            have h_27090 : Litex.In _value_i2 (Litex.Q (M := M)) := h_27090
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_27091)
            have h_27091 : Litex.In _value_i3 (Litex.Q (M := M)) := h_27091
            change (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_27090) (Litex.rationalToComplex _value_i3 h_27091))
              exact Litex.In _atomic_wd_1_0 (Litex.Q (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.mul _value_i2 _value_i3 (Litex.rationalToComplex _value_i2 h_27090) (Litex.rationalToComplex _value_i3 h_27091))
              exact (Litex.mulInQ _value_i2 _value_i3 h_27090 h_27091))));
          let _wd_2_1 := _value_i10;
          let _wd_2_2 := _object_w56;
          (Litex.call2 Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_2_0 _wd_2_1 _wd_2_2 (Litex.formulaFnInFnSet _wd_2_0) h_22034 (by
            let _atomic_wd_1_0 := _object_w56
            exact (Litex.mulInQ _value_i11 _value_i12 h_22035 h_22036)) True.intro))
          have h_22017 : (by
            let _equal_wd_2_0 := _object_w60
            let _equal_wd_2_1 := _object_w61
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show @Eq M.Value _ _ from Eq.refl _) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) (show @Eq M.Value _ _ from Eq.refl _) h_22014))
                )
            )
          let _object_w62 := (let _wd_2_0 := _value_i10;
          let _wd_2_1 := _object_w56;
          (Litex.mul _wd_2_0 _wd_2_1 (Litex.rationalToComplex _wd_2_0 h_22034) (by
            let _atomic_wd_1_0 := _object_w56
            exact (Litex.mulInC _value_i11 _value_i12 (Litex.rationalToComplex _value_i11 h_22035) (Litex.rationalToComplex _value_i12 h_22036)))))
          have h_22018 : (by
            let _equal_wd_2_0 := _object_w61
            let _equal_wd_2_1 := _object_w62
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12))])) = (M.mulValue (Litex.denote _value_i10) (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12))) from by
                    have _litex_residual : (M.mulValue (Litex.denote _value_i10) (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12))) = (M.mulValue (Litex.denote _value_i10) (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FunctionSemantics.graphValue (M := M) (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.rational), (M.standard Litex.StandardSetValue.rational)]) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (M.standard Litex.StandardSetValue.rational) (fun (_captured_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _captured_input (M.number (2 : ℂ))))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i10), (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12))])) = (M.mulValue (Litex.denote _value_i10) (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12))) from by
                    let _litex_original := _object_w61
                    let _litex_literal := _object_w61
                    have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (show @Eq M.Value _ _ from Eq.refl _) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
                    have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.rational Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.rational) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
                    exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.mulValue _raw_i2 _raw_i3)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = (M.mulValue (Litex.denote _value_i10) (M.mulValue (Litex.denote _value_i11) (Litex.denote _value_i12))) from rfl))
                  ))).trans _litex_residual)
                )
            )
          have h_22019 : (by
            let _equal_wd_2_0 := _object_w59
            let _equal_wd_2_1 := _object_w62
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.sameOfDenoteNumber _ _ (((Litex.NativeBridge.asComplex _value_i10 (Litex.rationalToComplex _value_i10 h_22034)) * (Litex.NativeBridge.asComplex _value_i11 (Litex.rationalToComplex _value_i11 h_22035))) * (Litex.NativeBridge.asComplex _value_i12 (Litex.rationalToComplex _value_i12 h_22036))) ((Litex.NativeBridge.asComplex _value_i10 (Litex.rationalToComplex _value_i10 h_22034)) * ((Litex.NativeBridge.asComplex _value_i11 (Litex.rationalToComplex _value_i11 h_22035)) * (Litex.NativeBridge.asComplex _value_i12 (Litex.rationalToComplex _value_i12 h_22036)))) (Litex.NativeBridge.denoteMul (_object_w59).val.left _value_i12 (_object_w59).wd.1 (_object_w59).wd.2 _ _ (Litex.NativeBridge.denoteMul _value_i10 _value_i11 (_object_w54).wd.1 (_object_w54).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.rationalToComplex _value_i10 h_22034)) (Litex.NativeBridge.asComplex_spec _value_i11 (Litex.rationalToComplex _value_i11 h_22035))) (Litex.NativeBridge.asComplex_spec _value_i12 (Litex.rationalToComplex _value_i12 h_22036))) (Litex.NativeBridge.denoteMul _value_i10 (_object_w62).val.right (_object_w62).wd.1 (_object_w62).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i10 (Litex.rationalToComplex _value_i10 h_22034)) (Litex.NativeBridge.denoteMul _value_i11 _value_i12 (_object_w56).wd.1 (_object_w56).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _value_i11 (Litex.rationalToComplex _value_i11 h_22035)) (Litex.NativeBridge.asComplex_spec _value_i12 (Litex.rationalToComplex _value_i12 h_22036)))) (by ring!))
                )
            )
          have h_22020 : (by
            let _equal_wd_2_0 := _object_w57
            let _equal_wd_2_1 := _object_w60
            exact Litex.Same _equal_wd_2_0 _equal_wd_2_1) :=
            (by
              litex_checked_step =>
                exact (
                  ((((((((h_22015).trans h_22016)).trans h_22019)).trans (h_22018).symm)).trans (h_22017).symm)
                )
            )
          exact (And.intro h_22013 (And.intro h_22014 (And.intro h_22015 (And.intro h_22016 (And.intro h_22017 (And.intro h_22018 (And.intro h_22019 h_22020)))))))
        );
        let h_28204 : (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact Litex.Subset _atomic_wd_1_0 (Litex.Q (M := M))) := (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          let _wd_2_1 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)));
          (let _setElement_0 := _wd_2_0;
            let _setElement_1 := _wd_2_1;
            let _setTail_2 := Litex.emptySet (M := M);
            let _setFresh_1 : ¬ Litex.In _setElement_1 _setTail_2 := (Litex.notInEmpty _setElement_1);
            let _setTail_1 := Litex.insert _setElement_1 _setTail_2 _setFresh_1;
            let _setFresh_0 : ¬ Litex.In _setElement_0 _setTail_1 := (Litex.notInInsert _setElement_0 _setElement_1 _setTail_2 _setFresh_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              let _atomic_wd_2_1 := _wd_2_1
              exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_2_0 _atomic_wd_2_1 ((1 : ℂ) / (2 : ℂ)) ((1 : ℂ) / (3 : ℂ)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_1).wd.1 (_atomic_wd_2_1).wd.2.1 (_atomic_wd_2_1).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))) (Litex.notInEmpty _setElement_0));
            let _setTail_0 := Litex.insert _setElement_0 _setTail_1 _setFresh_0;
            _setTail_0))
          exact (by
            let _set := _atomic_wd_1_0
            exact (Litex.insertSubset _set.val.element _set.val.tail (Litex.Q (M := M)) _set.wd (by
            let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_3 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (2 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (2 : ℂ)) ((1 : ℚ) / (2 : ℚ)) (by norm_num)))) (Litex.insertSubset _set.val.tail.val.element _set.val.tail.val.tail (Litex.Q (M := M)) _set.val.tail.wd (by
            let _atomic_wd_2_0 := (Litex.div (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (3 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (3 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 ((1 : ℂ) / (3 : ℂ)) (Litex.Q (M := M)) (Litex.NativeBridge.denoteDiv (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (_atomic_wd_2_0).wd.1 (_atomic_wd_2_0).wd.2.1 (_atomic_wd_2_0).wd.2.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInQOfEq ((1 : ℂ) / (3 : ℂ)) ((1 : ℚ) / (3 : ℚ)) (by norm_num)))) (Litex.emptySubset (Litex.Q (M := M)))))));
        Litex.finiteFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.rational Litex.StandardSetValue.rational (fun (_raw_i1 : M.Value) => True)) h_19022 (Litex.formulaFnInFnSet _wd_1_1) (Litex.formulaFnInFnSet _wd_1_2) h_19036 (fun i hi => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.rational) (Litex.denote (Litex.Q (M := M))) (M.standard_isSet Litex.StandardSetValue.rational) (Litex.isSet (Litex.Q (M := M))) (fun (_raw_i1 : M.Value) => True) i).mpr ⟨h_28204 i hi, True.intro⟩) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x1 _fold_h1 => (And.right (And.right (And.right (h_19041 _fold_x0 _fold_h0 _fold_x1 _fold_h1)))))))) (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x0 _fold_h0 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x1 _fold_h1 => (Litex.forallMembersOfRepresentations.{u, _, 0} (Litex.Q (M := M)) (fun _fold_x2 _fold_h2 => (And.right (And.right (And.right (And.right (And.right (And.right (And.right (h_22021 _fold_x0 _fold_h0 _fold_x1 _fold_h1 _fold_x2 _fold_h2))))))))))))))))
          let _right := _equal_wd_1_0
          exact (show Litex.Same _left _right from rfl))) (Eq.trans (h_18897 (M := M)) (Litex.sameRefl _equal_wd_1_1)))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_rational_x5f_fold_x2f_statement_x2e_lit
