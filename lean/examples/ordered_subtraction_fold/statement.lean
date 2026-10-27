import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_ordered_x5f_subtraction_x5f_fold_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_w9 := (let _wd_1_0 := (Litex.number (M := M) (1 : ℂ));
let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
let _wd_1_2 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
  intro _raw_i1 h_15 _
  let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_15)
  have h_15 : Litex.In _value_i1 (Litex.Z (M := M)) := h_15
  change Litex.In _value_i1 (Litex.Z (M := M))
  exact h_15));
let _wd_1_3 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (by
  intro _raw_i2 _raw_i3 h_34 h_35 _
  let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_34)
  have h_34 : Litex.In _value_i2 (Litex.Z (M := M)) := h_34
  let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_35)
  have h_35 : Litex.In _value_i3 (Litex.Z (M := M)) := h_35
  change (by
    let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_34) (Litex.integerToComplex _value_i3 h_35))
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_34) (Litex.integerToComplex _value_i3 h_35))
    exact (Litex.subInZ _value_i2 _value_i3 h_34 h_35))));
let _wd_1_4 := (Litex.number (M := M) (0 : ℂ));
(let h_117 : Litex.In _wd_1_0 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num));
let h_118 : Litex.In _wd_1_1 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num));
let h_119 : Litex.In _wd_1_4 (Litex.Z (M := M)) := (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num));
Litex.rangeFold _wd_1_0 _wd_1_1 _wd_1_2 _wd_1_3 _wd_1_4 (Litex.FunctionSignature.one (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True)) h_117 h_118 (Litex.formulaFnInFnSet _wd_1_2) (Litex.formulaFnInFnSet _wd_1_3) h_119 (fun k hlow hhigh => (Litex.FunctionSignature.withGuard_domain (M.standard Litex.StandardSetValue.integer) (Litex.denote (Litex.Z (M := M))) (M.standard_isSet Litex.StandardSetValue.integer) (Litex.isSet (Litex.Z (M := M))) (fun (_raw_i1 : M.Value) => True) (M.number (k : ℂ))).mpr ⟨Litex.integerInUnboundedCarrier .integer (by decide) k, True.intro⟩)))

noncomputable def _object_w10 := (Litex.neg (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)))

theorem h_1 : (by
  let _equal_wd_1_0 := (_object_w9 (M := M))
  let _equal_wd_1_1 := (_object_w10 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w9 (M := M));
        let _equal_wd_1_1 := (_object_w10 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from ((show (Litex.denote _equal_wd_1_0) = M.number (-6 : ℂ) from (by
          let _fold := _equal_wd_1_0
          have _seed : Litex.denote _fold.val.seed = M.number (0 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))
          have _term_0 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.function) (M.number (1 : ℂ)) = M.number (1 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_127 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_127)
            have h_127 : Litex.In _value_i1 (Litex.Z (M := M)) := h_127
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_127));
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.argument = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (1 : ℂ)) := by change (fun (_raw_i1 : M.Value) => _raw_i1) (Litex.denote _call.val.argument) = (M.number (1 : ℂ)); norm_num [_argument_0, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.number (1 : ℂ)) = M.number (1 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument_0).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _step_0 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.operation) (Litex.FiniteFunction.pack2 (M.number (0 : ℂ)) (M.number (1 : ℂ))) = M.number (-1 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_136 h_137 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_136)
            have h_136 : Litex.In _value_i2 (Litex.Z (M := M)) := h_136
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_137)
            have h_137 : Litex.In _value_i3 (Litex.Z (M := M)) := h_137
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_136) (Litex.integerToComplex _value_i3 h_137))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_136) (Litex.integerToComplex _value_i3 h_137))
              exact (Litex.subInZ _value_i2 _value_i3 h_136 h_137))));
          let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (1 : ℂ));
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (0 : ℂ) (0 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.operation
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _ _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.first = M.number (0 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))).trans (congrArg M.number (by norm_num : (0 : ℂ) = (0 : ℂ)))
            have _argument_1 : Litex.denote _call.val.second = M.number (1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))).trans (congrArg M.number (by norm_num : (1 : ℂ) = (1 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) = (M.subValue (M.number (0 : ℂ)) (M.number (1 : ℂ))) := by change (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).1 (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).2 = (M.subValue (M.number (0 : ℂ)) (M.number (1 : ℂ))); norm_num [Litex.FiniteFunction.unpack_pack2, _argument_0, _argument_1, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.subValue (M.number (0 : ℂ)) (M.number (1 : ℂ))) = M.number (-1 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) _argument_0 _argument_1)).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _term_1 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.function) (M.number (2 : ℂ)) = M.number (2 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_223 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_223)
            have h_223 : Litex.In _value_i1 (Litex.Z (M := M)) := h_223
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_223));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.argument = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (2 : ℂ)) := by change (fun (_raw_i1 : M.Value) => _raw_i1) (Litex.denote _call.val.argument) = (M.number (2 : ℂ)); norm_num [_argument_0, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.number (2 : ℂ)) = M.number (2 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument_0).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _step_1 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.operation) (Litex.FiniteFunction.pack2 (M.number (-1 : ℂ)) (M.number (2 : ℂ))) = M.number (-3 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_232 h_233 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_232)
            have h_232 : Litex.In _value_i2 (Litex.Z (M := M)) := h_232
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_233)
            have h_233 : Litex.In _value_i3 (Litex.Z (M := M)) := h_233
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_232) (Litex.integerToComplex _value_i3 h_233))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_232) (Litex.integerToComplex _value_i3 h_233))
              exact (Litex.subInZ _value_i2 _value_i3 h_232 h_233))));
          let _wd_1_1 := (Litex.number (M := M) (-1 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (2 : ℂ));
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (-1 : ℂ) (-1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.operation
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _ _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.first = M.number (-1 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (-1 : ℂ))).trans (congrArg M.number (by norm_num : (-1 : ℂ) = (-1 : ℂ)))
            have _argument_1 : Litex.denote _call.val.second = M.number (2 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))).trans (congrArg M.number (by norm_num : (2 : ℂ) = (2 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) = (M.subValue (M.number (-1 : ℂ)) (M.number (2 : ℂ))) := by change (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).1 (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).2 = (M.subValue (M.number (-1 : ℂ)) (M.number (2 : ℂ))); norm_num [Litex.FiniteFunction.unpack_pack2, _argument_0, _argument_1, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.subValue (M.number (-1 : ℂ)) (M.number (2 : ℂ))) = M.number (-3 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) _argument_0 _argument_1)).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _term_2 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.function) (M.number (3 : ℂ)) = M.number (3 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) (fun (_raw_i1 : M.Value) => _raw_i1) (by
            intro _raw_i1 h_319 _
            let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_319)
            have h_319 : Litex.In _value_i1 (Litex.Z (M := M)) := h_319
            change Litex.In _value_i1 (Litex.Z (M := M))
            exact h_319));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.function
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote _call.val.argument)) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.denote _call.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i1 : M.Value) => True) _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.argument = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.denote _call.val.argument) = (M.number (3 : ℂ)) := by change (fun (_raw_i1 : M.Value) => _raw_i1) (Litex.denote _call.val.argument) = (M.number (3 : ℂ)); norm_num [_argument_0, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.number (3 : ℂ)) = M.number (3 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) _argument_0).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          have _step_2 : Litex.FunctionSemantics.callValue (Litex.denote _fold.val.operation) (Litex.FiniteFunction.pack2 (M.number (-3 : ℂ)) (M.number (3 : ℂ))) = M.number (-6 : ℂ) := (by
            let _call := (let _wd_1_0 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (by
            intro _raw_i2 _raw_i3 h_328 h_329 _
            let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_328)
            have h_328 : Litex.In _value_i2 (Litex.Z (M := M)) := h_328
            let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_329)
            have h_329 : Litex.In _value_i3 (Litex.Z (M := M)) := h_329
            change (by
              let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_328) (Litex.integerToComplex _value_i3 h_329))
              exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
            exact (by
              let _atomic_wd_1_0 := (Litex.sub _value_i2 _value_i3 (Litex.integerToComplex _value_i2 h_328) (Litex.integerToComplex _value_i3 h_329))
              exact (Litex.subInZ _value_i2 _value_i3 h_328 h_329))));
          let _wd_1_1 := (Litex.number (M := M) (-3 : ℂ));
          let _wd_1_2 := (Litex.number (M := M) (3 : ℂ));
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _wd_1_0 _wd_1_1 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (-3 : ℂ) (-3 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)) True.intro))
            let _literal := (_equal_wd_1_0).val.operation
            have _head : Litex.Same _call.val.function _literal := (show @Eq M.Value _ _ from Eq.refl _)
            have _head_call := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))) _head
            have _beta := Litex.FunctionSemantics.call_graphValue _ _ _ _literal.wd (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _ _).mpr _call.wd.2)
            have _argument_0 : Litex.denote _call.val.first = M.number (-3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (-3 : ℂ))).trans (congrArg M.number (by norm_num : (-3 : ℂ) = (-3 : ℂ)))
            have _argument_1 : Litex.denote _call.val.second = M.number (3 : ℂ) := ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = (3 : ℂ)))
            have _body : _literal.val.bodyValue (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second)) = (M.subValue (M.number (-3 : ℂ)) (M.number (3 : ℂ))) := by change (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.subValue _raw_i2 _raw_i3)) (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).1 (Litex.FiniteFunction.unpack2 (Litex.FiniteFunction.pack2 (Litex.denote _call.val.first) (Litex.denote _call.val.second))).2 = (M.subValue (M.number (-3 : ℂ)) (M.number (3 : ℂ))); norm_num [Litex.FiniteFunction.unpack_pack2, _argument_0, _argument_1, Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            have _calculated : (M.subValue (M.number (-3 : ℂ)) (M.number (3 : ℂ))) = M.number (-6 : ℂ) := by norm_num [Litex.Semantics.add_numbers, Litex.Semantics.sub_numbers, Litex.Semantics.mul_numbers, Litex.Semantics.neg_numbers, Litex.Semantics.div_numbers]
            exact (congrArg (fun x => Litex.FunctionSemantics.callValue (Litex.denote _call.val.function) x) (congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) _argument_0 _argument_1)).symm.trans (_head_call.trans (_beta.trans (_body.trans _calculated))))
          apply Litex.rangeFoldDenote _fold (1 : ℤ) (3 : ℤ) ((Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ)).trans (congrArg M.number (by norm_num))) ((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)).trans (congrArg M.number (by norm_num))) (M.number (-6 : ℂ))
          have _indices : Litex.integerFoldIndices (1 : ℤ) (3 : ℤ) = [(1 : ℤ), (2 : ℤ), (3 : ℤ)] := by decide
          norm_num [Litex.foldValue, Litex.foldApply2, _indices, _seed, _term_0, _step_0, _term_1, _step_1, _term_2, _step_2]))).trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (6 : ℂ)) (_equal_wd_1_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)))).trans (congrArg M.number (by norm_num : (- (6 : ℂ)) = (-6 : ℂ)))).symm)))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_ordered_x5f_subtraction_x5f_fold_x2f_statement_x2e_lit
