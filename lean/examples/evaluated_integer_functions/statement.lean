import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_integer_x5f_functions_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFnOn (let _litex_output := (Litex.Z (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.Z (M := M))), (Litex.denote (Litex.NPos (M := M)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.Z (M := M))), (Litex.denote (Litex.NPos (M := M)))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.Z (M := M)))
  have _finiteProof_1 := (Litex.isSet (Litex.NPos (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue (M.mulValue _raw_i3 ((Litex.integerDivisionValue (M := M) true) _raw_i2 _raw_i3)) ((Litex.integerDivisionValue (M := M) false) _raw_i2 _raw_i3))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
  have _litex_checked_return : ∀ (_raw_i2 : M.Value) (_raw_i3 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.Z (M := M))) → M.mem _raw_i3 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _raw_i2 _raw_i3) → M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue (M.mulValue _raw_i3 ((Litex.integerDivisionValue (M := M) true) _raw_i2 _raw_i3)) ((Litex.integerDivisionValue (M := M) false) _raw_i2 _raw_i3))) _raw_i2 _raw_i3) (Litex.denote (Litex.Z (M := M))) := (by
    intro _raw_i2 _raw_i3 h_27 h_28 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_27)
    have h_27 : Litex.In _value_i2 (Litex.Z (M := M)) := h_27
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_28)
    have h_28 : Litex.In _value_i3 (Litex.NPos (M := M)) := h_28
    have h_29 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inNPos_positive _value_i3 h_28)
          )
      )
    have h_30 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i3 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i3 h_29)
          )
      )
    have h_31 : ¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i3 h_29) _litex_zero.symm)
          )
      )
    change (by
      let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := _value_i3;
      let _wd_2_1 := (Litex.quot _value_i2 _wd_2_0 h_27 h_28);
      (Litex.mul _wd_2_0 _wd_2_1 (Litex.naturalToComplex _wd_2_0 (Litex.inNPos_natural _wd_2_0 h_28)) (by
        let _atomic_wd_2_0 := _wd_2_1
        exact (Litex.integerToComplex _atomic_wd_2_0 (Litex.quotInZ _atomic_wd_2_0)))));
      let _wd_1_1 := (Litex.mod _value_i2 _value_i3 h_27 (Litex.naturalToInteger _value_i3 (Litex.inNPos_natural _value_i3 h_28)) h_31);
      (Litex.add _wd_1_0 _wd_1_1 (by
        let _atomic_wd_2_0 := _wd_1_0
        exact (Litex.mulInC _value_i3 (_atomic_wd_2_0).val.right (Litex.naturalToComplex _value_i3 (Litex.inNPos_natural _value_i3 h_28)) (Litex.integerToComplex (_atomic_wd_2_0).val.right (Litex.quotInZ (_atomic_wd_2_0).val.right)))) (by
        let _atomic_wd_2_0 := _wd_1_1
        exact (Litex.integerToComplex _atomic_wd_2_0 (Litex.modInZ _atomic_wd_2_0)))))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := _value_i3;
      let _wd_2_1 := (Litex.quot _value_i2 _wd_2_0 h_27 h_28);
      (Litex.mul _wd_2_0 _wd_2_1 (Litex.naturalToComplex _wd_2_0 (Litex.inNPos_natural _wd_2_0 h_28)) (by
        let _atomic_wd_2_0 := _wd_2_1
        exact (Litex.integerToComplex _atomic_wd_2_0 (Litex.quotInZ _atomic_wd_2_0)))));
      let _wd_1_1 := (Litex.mod _value_i2 _value_i3 h_27 (Litex.naturalToInteger _value_i3 (Litex.inNPos_natural _value_i3 h_28)) h_31);
      (Litex.add _wd_1_0 _wd_1_1 (by
        let _atomic_wd_2_0 := _wd_1_0
        exact (Litex.mulInC _value_i3 (_atomic_wd_2_0).val.right (Litex.naturalToComplex _value_i3 (Litex.inNPos_natural _value_i3 h_28)) (Litex.integerToComplex (_atomic_wd_2_0).val.right (Litex.quotInZ (_atomic_wd_2_0).val.right)))) (by
        let _atomic_wd_2_0 := _wd_1_1
        exact (Litex.integerToComplex _atomic_wd_2_0 (Litex.modInZ _atomic_wd_2_0)))))
      exact (Litex.addInZ (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.mulInZ _value_i3 ((_atomic_wd_1_0).val.left).val.right (Litex.naturalToInteger _value_i3 (Litex.inNPos_natural _value_i3 h_28)) (Litex.quotInZ ((_atomic_wd_1_0).val.left).val.right)) (Litex.modInZ (_atomic_wd_1_0).val.right))))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.Z (M := M))), (Litex.denote (Litex.NPos (M := M)))]) (Litex.denote (Litex.Z (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.Z (M := M))), (Litex.denote (Litex.NPos (M := M)))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.Z (M := M)))
  have _finiteProof_1 := (Litex.isSet (Litex.NPos (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet (Litex.Z (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
  exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard))
theorem h_508 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_509 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

theorem h_528 : (by
  let _equal_wd_1_0 := (let _object_w11 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)));
  let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
  (let _litex_call_arg_0 := _object_w11;
  let _litex_call_arg_1 := _wd_1_1;
  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_508 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_0 := _object_w11
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (7 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_object_w11).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (7 : ℂ)) (-7 : ℤ) (by norm_num)))) (Litex.numberInNPosOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num) (by norm_num))), True.intro⟩)))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (-7 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _object_w11 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)));
        let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
        (let _litex_call_arg_0 := _object_w11;
        let _litex_call_arg_1 := _wd_1_1;
        Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_508 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
          let _atomic_wd_1_0 := _object_w11
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (7 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_object_w11).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (7 : ℂ)) (-7 : ℤ) (by norm_num)))) (Litex.numberInNPosOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num) (by norm_num))), True.intro⟩)));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (-7 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (-7 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.negValue (M.number (7 : ℂ))), (M.number (3 : ℂ))])) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i1 (M := M)) = (Litex.denote (_object_i1 (M := M))) from rfl) (congrArg₂ (fun x y => Litex.FiniteFunction.tupleValue (M := M) ![x,y]) (show Litex.denote (_equal_wd_1_0).val.argument.val.first = (M.negValue (M.number (7 : ℂ))) from Eq.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) ((_equal_wd_1_0).val.argument.val.first).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)))).trans (congrArg M.number (by norm_num : (- (7 : ℂ)) = (-7 : ℂ)))) (Eq.symm (show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num))))))) (show Litex.denote (Litex.number (M := M) (3 : ℂ)) = (M.number (3 : ℂ)) from rfl))) (((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.negValue (M.number (7 : ℂ))), (M.number (3 : ℂ))])))).trans (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.negValue (M.number (7 : ℂ))), (M.number (3 : ℂ))])) = (M.addValue (M.mulValue (M.number (3 : ℂ)) ((Litex.integerDivisionValue (M := M) true) (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ)))) ((Litex.integerDivisionValue (M := M) false) (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ)))) from by
          let _litex_original := (let _object_w10 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)));
        let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
        (let _litex_call_arg_0 := _object_w10;
        let _litex_call_arg_1 := _wd_1_1;
        Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_508 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
          let _atomic_wd_1_0 := _object_w10
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (7 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_object_w10).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (7 : ℂ)) (-7 : ℤ) (by norm_num)))) (Litex.numberInNPosOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num) (by norm_num))), True.intro⟩)))
          let _litex_formula := (_object_i1 (M := M))
          have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := (h_509 (M := M))
          have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.denote _litex_original.val.argument)) _litex_head_eq
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.denote _litex_original.val.argument) _litex_original.wd.2
          exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue (M.mulValue _raw_i3 ((Litex.integerDivisionValue (M := M) true) _raw_i2 _raw_i3)) ((Litex.integerDivisionValue (M := M) false) _raw_i2 _raw_i3))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote _litex_original.val.argument) = (M.addValue (M.mulValue (M.number (3 : ℂ)) ((Litex.integerDivisionValue (M := M) true) (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ)))) ((Litex.integerDivisionValue (M := M) false) (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ)))); exact (congrArg₂ (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (M.addValue (M.mulValue _raw_i3 ((Litex.integerDivisionValue (M := M) true) _raw_i2 _raw_i3)) ((Litex.integerDivisionValue (M := M) false) _raw_i2 _raw_i3))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(M.negValue (M.number (7 : ℂ))), (M.number (3 : ℂ))]) (M.number (1 : ℂ)) = (M.negValue (M.number (7 : ℂ))) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(M.negValue (M.number (7 : ℂ))), (M.number (3 : ℂ))] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(M.negValue (M.number (7 : ℂ))), (M.number (3 : ℂ))]) (M.number (2 : ℂ)) = (M.number (3 : ℂ)) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(M.negValue (M.number (7 : ℂ))), (M.number (3 : ℂ))] (1 : Fin 2)))))
        )).trans (((Eq.refl (M.addValue (M.mulValue (M.number (3 : ℂ)) ((Litex.integerDivisionValue (M := M) true) (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ)))) ((Litex.integerDivisionValue (M := M) false) (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ)))))).trans (show (M.addValue (M.mulValue (M.number (3 : ℂ)) ((Litex.integerDivisionValue (M := M) true) (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ)))) ((Litex.integerDivisionValue (M := M) false) (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ)))) = M.number (-7 : ℂ) from ((congrArg₂ M.addValue (show (M.mulValue (M.number (3 : ℂ)) ((Litex.integerDivisionValue (M := M) true) (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ)))) = M.number (-9 : ℂ) from ((congrArg₂ M.mulValue (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num))) (show ((Litex.integerDivisionValue (M := M) true) (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ))) = M.number (-3 : ℂ) from (congrArg₂ (Litex.integerDivisionValue (M := M) true) (show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num))))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans (by
          have _numeric := Litex.integerDivisionValue_numbers true (M := M) (-7 : ℤ) (3 : ℤ)
          norm_num [Int.gcd_eq_natAbs_gcd_natAbs, Int.lcm_eq_natAbs_lcm_natAbs] at _numeric
          exact _numeric))).trans ((M.mul_numbers (3 : ℂ) (-3 : ℂ)).trans (congrArg M.number (by norm_num))))) (show ((Litex.integerDivisionValue (M := M) false) (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ))) = M.number (2 : ℂ) from (congrArg₂ (Litex.integerDivisionValue (M := M) false) (show (M.negValue (M.number (7 : ℂ))) = M.number (-7 : ℂ) from ((congrArg M.negValue (show (M.number (7 : ℂ)) = M.number (7 : ℂ) from (congrArg M.number (show (7 : ℂ) = (7 : ℂ) from by norm_num)))).trans ((M.neg_numbers (7 : ℂ)).trans (congrArg M.number (by norm_num))))) (show (M.number (3 : ℂ)) = M.number (3 : ℂ) from (congrArg M.number (show (3 : ℂ) = (3 : ℂ) from by norm_num)))).trans (by
          have _numeric := Litex.integerDivisionValue_numbers false (M := M) (-7 : ℤ) (3 : ℤ)
          norm_num [Int.gcd_eq_natAbs_gcd_natAbs, Int.lcm_eq_natAbs_lcm_natAbs] at _numeric
          exact _numeric))).trans ((M.add_numbers (-9 : ℂ) (2 : ℂ)).trans (congrArg M.number (by norm_num)))))))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (-7 : ℂ))).trans (congrArg M.number (by norm_num : (-7 : ℂ) = (-7 : ℂ)))).symm)))
      )
  )

theorem h_538 : (by
  let _equal_wd_1_0 := (let _object_w11 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)));
  let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
  (let _litex_call_arg_0 := _object_w11;
  let _litex_call_arg_1 := _wd_1_1;
  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_508 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_0 := _object_w11
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (7 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_object_w11).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (7 : ℂ)) (-7 : ℤ) (by norm_num)))) (Litex.numberInNPosOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num) (by norm_num))), True.intro⟩)))
  let _equal_wd_1_1 := (Litex.number (M := M) (-7 : ℂ))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (h_528 (M := M))
      )
  )

noncomputable def _object_i4 := (Litex.formulaFn (M := M) Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i5 : M.Value) => True) (fun (_raw_i5 : M.Value) => (Litex.factorialValue (M := M) _raw_i5)) (by
  intro _raw_i5 h_553 _
  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_553)
  have h_553 : Litex.In _value_i5 (Litex.N (M := M)) := h_553
  have h_554 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i5 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.naturalNonnegative _value_i5 h_553)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.factorial _value_i5 h_553)
    exact Litex.In _atomic_wd_1_0 (Litex.N (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.factorial _value_i5 h_553)
    exact (Litex.inNPos_natural _atomic_wd_1_0 (Litex.factorialInNPos _atomic_wd_1_0)))))
theorem h_577 : Litex.In (_object_i4 (M := M)) (Litex.fnSet ((_object_i4 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i4 (M := M)))
      )
  )
theorem h_578 : Litex.Same (_object_i4 (M := M)) (_object_i4 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i4 (M := M)))
      )
  )

theorem h_589 : (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i5 : M.Value) => True) (_object_i4 (M := M)) (Litex.number (M := M) (5 : ℂ)) (h_577 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (5 : ℂ) (5 : ℕ) (by norm_num)) True.intro)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (120 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i5 : M.Value) => True) (_object_i4 (M := M)) (Litex.number (M := M) (5 : ℂ)) (h_577 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (5 : ℂ) (5 : ℕ) (by norm_num)) True.intro);
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (120 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (120 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (M.number (5 : ℂ))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i4 (M := M)) = (Litex.denote (_object_i4 (M := M))) from rfl) (show Litex.denote (Litex.number (M := M) (5 : ℂ)) = (M.number (5 : ℂ)) from rfl)) (((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (M.number (5 : ℂ))))).trans (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (M.number (5 : ℂ))) = ((Litex.factorialValue (M := M)) (M.number (5 : ℂ))) from by
          let _litex_original := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i5 : M.Value) => True) (_object_i4 (M := M)) (Litex.number (M := M) (5 : ℂ)) (h_577 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (5 : ℂ) (5 : ℕ) (by norm_num)) True.intro)
          let _litex_formula := (_object_i4 (M := M))
          have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := (h_578 (M := M))
          have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.denote _litex_original.val.argument)) _litex_head_eq
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.denote _litex_original.val.argument) ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i5 : M.Value) => True) _).mpr _litex_original.wd.2)
          exact (Eq.symm (show Litex.denote (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i5 : M.Value) => True) (_object_i4 (M := M)) (Litex.number (M := M) (5 : ℂ)) (h_577 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (5 : ℂ) (5 : ℕ) (by norm_num)) True.intro) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (M.number (5 : ℂ))) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i4 (M := M)) = (Litex.denote (_object_i4 (M := M))) from rfl) (show Litex.denote (Litex.number (M := M) (5 : ℂ)) = (M.number (5 : ℂ)) from rfl))).trans (_litex_call_eq.trans (_litex_beta.trans (show _litex_formula.val.bodyValue (Litex.denote _litex_original.val.argument) = ((Litex.factorialValue (M := M)) (M.number (5 : ℂ))) from congrArg (fun (_raw_i5 : M.Value) => (Litex.factorialValue (M := M) _raw_i5)) (show Litex.denote (Litex.number (M := M) (5 : ℂ)) = (M.number (5 : ℂ)) from rfl))))
        )).trans (((Eq.refl ((Litex.factorialValue (M := M)) (M.number (5 : ℂ))))).trans (show ((Litex.factorialValue (M := M)) (M.number (5 : ℂ))) = M.number (120 : ℂ) from (congrArg (Litex.factorialValue (M := M)) (show (M.number (5 : ℂ)) = M.number (5 : ℂ) from (congrArg M.number (show (5 : ℂ) = (5 : ℂ) from by norm_num)))).trans (by
          have _numeric := Litex.factorialValue_number (M := M) (5 : ℕ)
          norm_num [Int.gcd_eq_natAbs_gcd_natAbs, Int.lcm_eq_natAbs_lcm_natAbs] at _numeric
          exact _numeric))))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (120 : ℂ))).trans (congrArg M.number (by norm_num : (120 : ℂ) = (120 : ℂ)))).symm)))
      )
  )

theorem h_595 : (by
  let _equal_wd_1_0 := (Litex.call Litex.StandardSetValue.natural Litex.StandardSetValue.natural (fun (_raw_i5 : M.Value) => True) (_object_i4 (M := M)) (Litex.number (M := M) (5 : ℂ)) (h_577 (M := M)) (Litex.NativeBridge.numberInNOfEq (M := M) (5 : ℂ) (5 : ℕ) (by norm_num)) True.intro)
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (120 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_589 (M := M))
      )
  )

noncomputable def _object_i6 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.natural (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => ((Litex.gcdLcmValue (M := M) true) _raw_i7 _raw_i8)) (by
  intro _raw_i7 _raw_i8 h_623 h_624 _
  let _value_i7 := Litex.semanticObject (M := M) _raw_i7 (M.member_isSet h_623)
  have h_623 : Litex.In _value_i7 (Litex.Z (M := M)) := h_623
  let _value_i8 := Litex.semanticObject (M := M) _raw_i8 (M.member_isSet h_624)
  have h_624 : Litex.In _value_i8 (Litex.Z (M := M)) := h_624
  change (by
    let _atomic_wd_1_0 := (Litex.lcm _value_i7 _value_i8 h_623 h_624)
    exact Litex.In _atomic_wd_1_0 (Litex.N (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.lcm _value_i7 _value_i8 h_623 h_624)
    exact (Litex.lcmInN _atomic_wd_1_0))))
theorem h_669 : Litex.In (_object_i6 (M := M)) (Litex.fnSet ((_object_i6 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i6 (M := M)))
      )
  )
theorem h_670 : Litex.Same (_object_i6 (M := M)) (_object_i6 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i6 (M := M)))
      )
  )

theorem h_713 : (by
  let _equal_wd_1_0 := (let _object_w28 := (Litex.neg (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)));
  let _wd_1_1 := (Litex.number (M := M) (15 : ℂ));
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.natural (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (_object_i6 (M := M)) _object_w28 _wd_1_1 (h_669 (M := M)) (by
    let _atomic_wd_1_0 := _object_w28
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (6 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (6 : ℂ)) (_object_w28).wd _ (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (6 : ℂ)) (-6 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (15 : ℂ) (15 : ℤ) (by norm_num)) True.intro))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (30 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (let _object_w28 := (Litex.neg (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)));
        let _wd_1_1 := (Litex.number (M := M) (15 : ℂ));
        (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.natural (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (_object_i6 (M := M)) _object_w28 _wd_1_1 (h_669 (M := M)) (by
          let _atomic_wd_1_0 := _object_w28
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (6 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (6 : ℂ)) (_object_w28).wd _ (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (6 : ℂ)) (-6 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (15 : ℂ) (15 : ℤ) (by norm_num)) True.intro));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (30 : ℂ)) from (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (30 : ℂ)) from ((Eq.trans (show Litex.denote _equal_wd_1_0 = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i6 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.negValue (M.number (6 : ℂ))), (M.number (15 : ℂ))])) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i6 (M := M)) = (Litex.denote (_object_i6 (M := M))) from rfl) (congrArg₂ (fun x y => Litex.FiniteFunction.tupleValue (M := M) ![x,y]) (show Litex.denote (_equal_wd_1_0).val.first = (M.negValue (M.number (6 : ℂ))) from Eq.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (6 : ℂ)) ((_equal_wd_1_0).val.first).wd _ (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)))).trans (congrArg M.number (by norm_num : (- (6 : ℂ)) = (-6 : ℂ)))) (Eq.symm (show (M.negValue (M.number (6 : ℂ))) = M.number (-6 : ℂ) from ((congrArg M.negValue (show (M.number (6 : ℂ)) = M.number (6 : ℂ) from (congrArg M.number (show (6 : ℂ) = (6 : ℂ) from by norm_num)))).trans ((M.neg_numbers (6 : ℂ)).trans (congrArg M.number (by norm_num))))))) (show Litex.denote (Litex.number (M := M) (15 : ℂ)) = (M.number (15 : ℂ)) from rfl))) (((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i6 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.negValue (M.number (6 : ℂ))), (M.number (15 : ℂ))])))).trans (((show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i6 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.negValue (M.number (6 : ℂ))), (M.number (15 : ℂ))])) = ((Litex.gcdLcmValue (M := M) true) (M.negValue (M.number (6 : ℂ))) (M.number (15 : ℂ))) from by
          let _litex_original := (let _object_w27 := (Litex.neg (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)));
        let _wd_1_1 := (Litex.number (M := M) (15 : ℂ));
        (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.natural (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (_object_i6 (M := M)) _object_w27 _wd_1_1 (h_669 (M := M)) (by
          let _atomic_wd_1_0 := _object_w27
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (6 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (6 : ℂ)) (_object_w27).wd _ (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (6 : ℂ)) (-6 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (15 : ℂ) (15 : ℤ) (by norm_num)) True.intro))
          let _litex_formula := (_object_i6 (M := M))
          have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := (h_670 (M := M))
          have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.FiniteFunction.pack2 (M := M) (Litex.denote _litex_original.val.first) (Litex.denote _litex_original.val.second))) _litex_head_eq
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.FiniteFunction.pack2 (M := M) (Litex.denote _litex_original.val.first) (Litex.denote _litex_original.val.second)) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.natural (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) _ _).mpr _litex_original.wd.2)
          exact (Eq.symm (show Litex.denote (let _object_w26 := (Litex.neg (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)));
        let _wd_1_1 := (Litex.number (M := M) (15 : ℂ));
        (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.natural (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (_object_i6 (M := M)) _object_w26 _wd_1_1 (h_669 (M := M)) (by
          let _atomic_wd_1_0 := _object_w26
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (6 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (6 : ℂ)) (_object_w26).wd _ (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (6 : ℂ)) (-6 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (15 : ℂ) (15 : ℤ) (by norm_num)) True.intro)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i6 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.negValue (M.number (6 : ℂ))), (M.number (15 : ℂ))])) from congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) (show Litex.denote (_object_i6 (M := M)) = (Litex.denote (_object_i6 (M := M))) from rfl) (congrArg₂ (fun x y => Litex.FiniteFunction.tupleValue (M := M) ![x,y]) (show Litex.denote (Litex.neg (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ))) = (M.negValue (M.number (6 : ℂ))) from Eq.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)))).trans (congrArg M.number (by norm_num : (- (6 : ℂ)) = (-6 : ℂ)))) (Eq.symm (show (M.negValue (M.number (6 : ℂ))) = M.number (-6 : ℂ) from ((congrArg M.negValue (show (M.number (6 : ℂ)) = M.number (6 : ℂ) from (congrArg M.number (show (6 : ℂ) = (6 : ℂ) from by norm_num)))).trans ((M.neg_numbers (6 : ℂ)).trans (congrArg M.number (by norm_num))))))) (show Litex.denote (Litex.number (M := M) (15 : ℂ)) = (M.number (15 : ℂ)) from rfl)))).trans (_litex_call_eq.trans (_litex_beta.trans (show _litex_formula.val.bodyValue (Litex.FiniteFunction.pack2 (M := M) (Litex.denote _litex_original.val.first) (Litex.denote _litex_original.val.second)) = ((Litex.gcdLcmValue (M := M) true) (M.negValue (M.number (6 : ℂ))) (M.number (15 : ℂ))) from (congrArg (fun (_pair : M.Value × M.Value) => (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => ((Litex.gcdLcmValue (M := M) true) _raw_i7 _raw_i8)) _pair.1 _pair.2) (Litex.FiniteFunction.unpack_pack2 (M := M) (Litex.denote _litex_original.val.first) (Litex.denote _litex_original.val.second))).trans (congrArg₂ (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => ((Litex.gcdLcmValue (M := M) true) _raw_i7 _raw_i8)) (show Litex.denote (Litex.neg (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ))) = (M.negValue (M.number (6 : ℂ))) from Eq.trans (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)))).trans (congrArg M.number (by norm_num : (- (6 : ℂ)) = (-6 : ℂ)))) (Eq.symm (show (M.negValue (M.number (6 : ℂ))) = M.number (-6 : ℂ) from ((congrArg M.negValue (show (M.number (6 : ℂ)) = M.number (6 : ℂ) from (congrArg M.number (show (6 : ℂ) = (6 : ℂ) from by norm_num)))).trans ((M.neg_numbers (6 : ℂ)).trans (congrArg M.number (by norm_num))))))) (show Litex.denote (Litex.number (M := M) (15 : ℂ)) = (M.number (15 : ℂ)) from rfl)))))
        )).trans (((Eq.refl ((Litex.gcdLcmValue (M := M) true) (M.negValue (M.number (6 : ℂ))) (M.number (15 : ℂ))))).trans (show ((Litex.gcdLcmValue (M := M) true) (M.negValue (M.number (6 : ℂ))) (M.number (15 : ℂ))) = M.number (30 : ℂ) from (congrArg₂ (Litex.gcdLcmValue (M := M) true) (show (M.negValue (M.number (6 : ℂ))) = M.number (-6 : ℂ) from ((congrArg M.negValue (show (M.number (6 : ℂ)) = M.number (6 : ℂ) from (congrArg M.number (show (6 : ℂ) = (6 : ℂ) from by norm_num)))).trans ((M.neg_numbers (6 : ℂ)).trans (congrArg M.number (by norm_num))))) (show (M.number (15 : ℂ)) = M.number (15 : ℂ) from (congrArg M.number (show (15 : ℂ) = (15 : ℂ) from by norm_num)))).trans (by
          have _numeric := Litex.gcdLcmValue_numbers true (M := M) (-6 : ℤ) (15 : ℤ)
          norm_num [Int.gcd_eq_natAbs_gcd_natAbs, Int.lcm_eq_natAbs_lcm_natAbs] at _numeric
          exact _numeric))))))).trans (((Litex.NativeBridge.denoteNumber (M := M) (30 : ℂ))).trans (congrArg M.number (by norm_num : (30 : ℂ) = (30 : ℂ)))).symm)))
      )
  )

theorem h_735 : (by
  let _equal_wd_1_0 := (let _object_w28 := (Litex.neg (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)));
  let _wd_1_1 := (Litex.number (M := M) (15 : ℂ));
  (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.natural (fun (_raw_i7 : M.Value) (_raw_i8 : M.Value) => True) (_object_i6 (M := M)) _object_w28 _wd_1_1 (h_669 (M := M)) (by
    let _atomic_wd_1_0 := _object_w28
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (6 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (6 : ℂ)) (_object_w28).wd _ (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (6 : ℂ)) (-6 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (15 : ℂ) (15 : ℤ) (by norm_num)) True.intro))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (30 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (h_713 (M := M))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_evaluated_x5f_integer_x5f_functions_x2f_statement_x2e_lit
