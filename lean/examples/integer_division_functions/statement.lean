import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_integer_x5f_division_x5f_functions_x2f_statement_x2e_lit

universe u v14
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFnOn (let _litex_output := (Litex.Z (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.Z (M := M))), (Litex.denote (Litex.NPos (M := M)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.Z (M := M))), (Litex.denote (Litex.NPos (M := M)))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.Z (M := M)))
  have _finiteProof_1 := (Litex.isSet (Litex.NPos (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => ((Litex.integerDivisionValue (M := M) true) _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
  have _litex_checked_return : ∀ (_raw_i2 : M.Value) (_raw_i3 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.Z (M := M))) → M.mem _raw_i3 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _raw_i2 _raw_i3) → M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => ((Litex.integerDivisionValue (M := M) true) _raw_i2 _raw_i3)) _raw_i2 _raw_i3) (Litex.denote (Litex.Z (M := M))) := (by
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
      let _atomic_wd_1_0 := (Litex.quot _value_i2 _value_i3 h_27 h_28)
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.quot _value_i2 _value_i3 h_27 h_28)
      exact (Litex.quotInZ _atomic_wd_1_0)))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.Z (M := M))), (Litex.denote (Litex.NPos (M := M)))]) (Litex.denote (Litex.Z (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.Z (M := M))), (Litex.denote (Litex.NPos (M := M)))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.Z (M := M)))
  have _finiteProof_1 := (Litex.isSet (Litex.NPos (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet (Litex.Z (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
  exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard))
theorem h_71 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_72 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_i4 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => ((Litex.integerDivisionValue (M := M) false) _raw_i5 _raw_i6)) (by
  intro _raw_i5 _raw_i6 h_141 h_142 h_73
  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_141)
  have h_141 : Litex.In _value_i5 (Litex.Z (M := M)) := h_141
  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_142)
  have h_142 : Litex.In _value_i6 (Litex.Z (M := M)) := h_142
  have h_73 : ¬ Litex.Same _value_i6 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (by
            change (¬ (_raw_i6 = (M.number (0 : ℂ))))
            exact h_73)
        )
    )
  change (by
    let _atomic_wd_1_0 := (Litex.mod _value_i5 _value_i6 h_141 h_142 h_73)
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.mod _value_i5 _value_i6 h_141 h_142 h_73)
    exact (Litex.modInZ _atomic_wd_1_0))))
theorem h_193 : Litex.In (_object_i4 (M := M)) (Litex.fnSet ((_object_i4 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i4 (M := M)))
      )
  )
theorem h_194 : Litex.Same (_object_i4 (M := M)) (_object_i4 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i4 (M := M)))
      )
  )

noncomputable def _object_i9 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) (fun (_raw_i10 : M.Value) => (M.addValue _raw_i10 (M.number (1 : ℂ)))) (by
  intro _raw_i10 h_208 _
  let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_208)
  have h_208 : Litex.In _value_i10 (Litex.Z (M := M)) := h_208
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i10 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i10 h_208) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i10 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i10 h_208) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.addInZ _value_i10 (Litex.number (M := M) (1 : ℂ)) h_208 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))))))
theorem h_285 : Litex.In (_object_i9 (M := M)) (Litex.fnSet ((_object_i9 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i9 (M := M)))
      )
  )
theorem h_286 : Litex.Same (_object_i9 (M := M)) (_object_i9 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i9 (M := M)))
      )
  )

noncomputable def _object_i11 := (Litex.formulaFnOn (let _litex_output := (Litex.Z (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.Z (M := M))), (Litex.denote (Litex.NPos (M := M)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.Z (M := M))), (Litex.denote (Litex.NPos (M := M)))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.Z (M := M)))
  have _finiteProof_1 := (Litex.isSet (Litex.NPos (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i12 : M.Value) (_raw_i13 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i12 : M.Value) (_raw_i13 : M.Value) => ((Litex.integerDivisionValue (M := M) true) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) _raw_i12) _raw_i13)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
  have _litex_checked_return : ∀ (_raw_i12 : M.Value) (_raw_i13 : M.Value), M.mem _raw_i12 (Litex.denote (Litex.Z (M := M))) → M.mem _raw_i13 (Litex.denote (Litex.NPos (M := M))) → ((fun (_raw_i12 : M.Value) (_raw_i13 : M.Value) => True) _raw_i12 _raw_i13) → M.mem ((fun (_raw_i12 : M.Value) (_raw_i13 : M.Value) => ((Litex.integerDivisionValue (M := M) true) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) _raw_i12) _raw_i13)) _raw_i12 _raw_i13) (Litex.denote (Litex.Z (M := M))) := (by
    intro _raw_i12 _raw_i13 h_313 h_314 _
    let _value_i12 := Litex.semanticObject (M := M) _raw_i12 (M.member_isSet h_313)
    have h_313 : Litex.In _value_i12 (Litex.Z (M := M)) := h_313
    let _value_i13 := Litex.semanticObject (M := M) _raw_i13 (M.member_isSet h_314)
    have h_314 : Litex.In _value_i13 (Litex.NPos (M := M)) := h_314
    have h_315 : Litex.Lt (Litex.number (M := M) (0 : ℂ)) _value_i13 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inNPos_positive _value_i13 h_314)
          )
      )
    have h_316 : Litex.Le (Litex.number (M := M) (0 : ℂ)) _value_i13 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.ltToLe (Litex.number (M := M) 0) _value_i13 h_315)
          )
      )
    have h_317 : ¬ Litex.Same _value_i13 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (fun _litex_zero => (Litex.ltNotSame (Litex.number (M := M) 0) _value_i13 h_315) _litex_zero.symm)
          )
      )
    change (by
      let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) (_object_i9 (M := M)) _value_i12 (h_285 (M := M)) h_313 True.intro);
      let _wd_1_1 := _value_i13;
      (Litex.quot _wd_1_0 _wd_1_1 (by
        let _atomic_wd_2_0 := _wd_1_0
        exact (by
          let _litex_return_call := _atomic_wd_2_0
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.callInOutput _litex_return_call))) h_314))
      exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
    exact (by
      let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) (_object_i9 (M := M)) _value_i12 (h_285 (M := M)) h_313 True.intro);
      let _wd_1_1 := _value_i13;
      (Litex.quot _wd_1_0 _wd_1_1 (by
        let _atomic_wd_2_0 := _wd_1_0
        exact (by
          let _litex_return_call := _atomic_wd_2_0
          exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.callInOutput _litex_return_call))) h_314))
      exact (Litex.quotInZ _atomic_wd_1_0)))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.Z (M := M))), (Litex.denote (Litex.NPos (M := M)))]) (Litex.denote (Litex.Z (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.Z (M := M))), (Litex.denote (Litex.NPos (M := M)))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.Z (M := M)))
  have _finiteProof_1 := (Litex.isSet (Litex.NPos (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet (Litex.Z (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i12 : M.Value) (_raw_i13 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
  exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard))
theorem h_497 : Litex.In (_object_i11 (M := M)) (Litex.fnSet ((_object_i11 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i11 (M := M)))
      )
  )
theorem h_498 : Litex.Same (_object_i11 (M := M)) (_object_i11 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i11 (M := M)))
      )
  )

noncomputable def _object_w37 := (let _object_w28 := (Litex.neg (Litex.number (M := M) (7 : ℂ)) (Litex.numberInC (M := M) (7 : ℂ)));
let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
(let _litex_call_arg_0 := _object_w28;
let _litex_call_arg_1 := _wd_1_1;
Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_71 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
  let _atomic_wd_1_0 := _object_w28
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (7 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_object_w28).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (7 : ℂ)) (-7 : ℤ) (by norm_num)))) (Litex.numberInNPosOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num) (by norm_num))), True.intro⟩)))

noncomputable def _object_w38 := (Litex.neg (Litex.number (M := M) (3 : ℂ)) (Litex.numberInC (M := M) (3 : ℂ)))

theorem h_499 : (by
  let _equal_wd_1_0 := (_object_w37 (M := M))
  let _equal_wd_1_1 := (_object_w38 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w37 (M := M));
        let _equal_wd_1_1 := (_object_w38 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.negValue (M.number (7 : ℂ))), (M.number (3 : ℂ))])) = (M.negValue (M.number (3 : ℂ))) from by
          have _litex_residual : ((Litex.integerDivisionValue (M := M) true) (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ))) = (M.negValue (M.number (3 : ℂ))) := (let _equal_wd_2_0 := (let _wd_1_0 := (_equal_wd_1_0).val.argument.val.first;
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          (Litex.quot _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (7 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (7 : ℂ)) (-7 : ℤ) (by norm_num)))) (Litex.numberInNPosOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num) (by norm_num))));
          let _equal_wd_2_1 := _equal_wd_1_1;
          (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 _equal_wd_2_1 (-3 : ℂ) (- (3 : ℂ)) (let _intop := _equal_wd_2_0;
          let _member : Litex.In _intop Litex.C := Litex.integerToComplex _intop (Litex.quotInZ _intop);
          (Litex.quotDenoteInt _intop (-7 : ℤ) (3 : ℤ) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) ((_equal_wd_2_0).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)))).trans (congrArg M.number (by norm_num : (- (7 : ℂ)) = ((-7 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = ((3 : ℤ) : ℂ))))).trans (congrArg M.number (by norm_num))) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) (_equal_wd_2_1).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.negValue (M.number (7 : ℂ))), (M.number (3 : ℂ))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.negValue (M.number (7 : ℂ))), (M.number (3 : ℂ))])) = ((Litex.integerDivisionValue (M := M) true) (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
        let _object_w36 := (_equal_wd_1_0).val.argument.val.first;
        let _wd_1_2 := (Litex.number (M := M) (3 : ℂ));
        (let _litex_call_arg_0 := _object_w36;
        let _litex_call_arg_1 := _wd_1_2;
        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.Z (M := M))), (Litex.denote (Litex.NPos (M := M)))] (by
          have _finiteProof_0 := (Litex.isSet (Litex.Z (M := M)))
          have _finiteProof_1 := (Litex.isSet (Litex.NPos (M := M)))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )) (Litex.Z (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _wd_1_0 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.formulaFnInFnSet _wd_1_0) (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
          let _atomic_wd_1_0 := _object_w36
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (7 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_object_w36).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (7 : ℂ)) (-7 : ℤ) (by norm_num)))) (Litex.numberInNPosOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num) (by norm_num))) True.intro))
          have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_72 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
          exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => ((Litex.integerDivisionValue (M := M) true) _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = ((Litex.integerDivisionValue (M := M) true) (M.negValue (M.number (7 : ℂ))) (M.number (3 : ℂ))); exact (congrArg₂ (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => ((Litex.integerDivisionValue (M := M) true) _raw_i2 _raw_i3)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(M.negValue (M.number (7 : ℂ))), (M.number (3 : ℂ))]) (M.number (1 : ℂ)) = (M.negValue (M.number (7 : ℂ))) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(M.negValue (M.number (7 : ℂ))), (M.number (3 : ℂ))] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(M.negValue (M.number (7 : ℂ))), (M.number (3 : ℂ))]) (M.number (2 : ℂ)) = (M.number (3 : ℂ)) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(M.negValue (M.number (7 : ℂ))), (M.number (3 : ℂ))] (1 : Fin 2)))))
        ))).trans _litex_residual)))
      )
  )

noncomputable def _object_w44 := (let _object_w39 := ((_object_w37 (M := M))).val.argument.val.first;
let _wd_1_1 := (_object_w38 (M := M));
(Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) (_object_i4 (M := M)) _object_w39 _wd_1_1 (h_193 (M := M)) (by
  let _atomic_wd_1_0 := _object_w39
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (7 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_object_w39).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (7 : ℂ)) (-7 : ℤ) (by norm_num)))) (by
  let _atomic_wd_1_0 := (_object_w38 (M := M))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (3 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) ((_object_w38 (M := M))).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (3 : ℂ)) (-3 : ℤ) (by norm_num)))) (by
  let _atomic_wd_1_0 := (_object_w38 (M := M))
  exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (- (3 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) ((_object_w38 (M := M))).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))))

theorem h_1023 : (by
  let _equal_wd_1_0 := (_object_w44 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w44 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.negValue (M.number (7 : ℂ))), (M.negValue (M.number (3 : ℂ)))])) = (M.number (2 : ℂ)) from by
          have _litex_residual : ((Litex.integerDivisionValue (M := M) false) (M.negValue (M.number (7 : ℂ))) (M.negValue (M.number (3 : ℂ)))) = (M.number (2 : ℂ)) := (let _equal_wd_2_0 := (let _wd_1_0 := (_equal_wd_1_0).val.first;
          let _wd_1_1 := (_object_w38 (M := M));
          (Litex.mod _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (7 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (7 : ℂ)) (-7 : ℤ) (by norm_num)))) (by
            let _atomic_wd_1_0 := (_object_w38 (M := M))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (3 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) ((_object_w38 (M := M))).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (3 : ℂ)) (-3 : ℤ) (by norm_num)))) (by
            let _atomic_wd_1_0 := (_object_w38 (M := M))
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (- (3 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) ((_object_w38 (M := M))).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (2 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (2 : ℂ) (let _intop := _equal_wd_2_0;
          let _member : Litex.In _intop Litex.C := Litex.integerToComplex _intop (Litex.modInZ _intop);
          (Litex.modDenoteInt _intop (-7 : ℤ) (-3 : ℤ) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) ((_equal_wd_2_0).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)))).trans (congrArg M.number (by norm_num : (- (7 : ℂ)) = ((-7 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) ((_object_w38 (M := M))).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)))).trans (congrArg M.number (by norm_num : (- (3 : ℂ)) = ((-3 : ℤ) : ℂ))))).trans (congrArg M.number (by norm_num))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.negValue (M.number (7 : ℂ))), (M.negValue (M.number (3 : ℂ)))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.negValue (M.number (7 : ℂ))), (M.negValue (M.number (3 : ℂ)))])) = ((Litex.integerDivisionValue (M := M) false) (M.negValue (M.number (7 : ℂ))) (M.negValue (M.number (3 : ℂ)))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i4 (M := M));
          let _object_w43 := (_equal_wd_1_0).val.first;
          let _wd_1_2 := (_object_w38 (M := M));
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) _wd_1_0 _object_w43 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_0 := _object_w43
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (7 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_object_w43).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (7 : ℂ)) (-7 : ℤ) (by norm_num)))) (by
            let _atomic_wd_1_0 := (_object_w38 (M := M))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (3 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) ((_object_w38 (M := M))).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (3 : ℂ)) (-3 : ℤ) (by norm_num)))) (by
            let _atomic_wd_1_0 := (_object_w38 (M := M))
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (- (3 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (3 : ℂ)) ((_object_w38 (M := M))).wd _ (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))))
          have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_194 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
          have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => ((Litex.integerDivisionValue (M := M) false) _raw_i5 _raw_i6)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => (¬ (_raw_i6 = (M.number (0 : ℂ))))) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => ((Litex.integerDivisionValue (M := M) false) _raw_i5 _raw_i6)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.integer) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => ((Litex.integerDivisionValue (M := M) false) _raw_i5 _raw_i6)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = ((Litex.integerDivisionValue (M := M) false) (M.negValue (M.number (7 : ℂ))) (M.negValue (M.number (3 : ℂ)))) from rfl))
        ))).trans _litex_residual)))
      )
  )

noncomputable def _object_w46 := (let _litex_call_arg_0 := (Litex.number (M := M) (6 : ℂ));
let _litex_call_arg_1 := (Litex.number (M := M) (3 : ℂ));
Litex.callOn ((_object_i11 (M := M))).val.signature (_object_i11 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_497 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (Litex.NativeBridge.numberInZOfEq (M := M) (6 : ℂ) (6 : ℤ) (by norm_num)) (Litex.numberInNPosOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num) (by norm_num))), True.intro⟩))

noncomputable def _object_w47 := (let _wd_1_0 := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) (_object_i9 (M := M)) (Litex.number (M := M) (6 : ℂ)) (h_285 (M := M)) (Litex.NativeBridge.numberInZOfEq (M := M) (6 : ℂ) (6 : ℤ) (by norm_num)) True.intro);
let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
(Litex.quot _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (by
    let _litex_return_call := _atomic_wd_1_0
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.numberInNPosOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num) (by norm_num))))

theorem h_1213 : (by
  let _equal_wd_1_0 := (_object_w46 (M := M))
  let _equal_wd_1_1 := (_object_w47 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w46 (M := M));
        let _equal_wd_1_1 := (_object_w47 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (6 : ℂ)), (M.number (3 : ℂ))])) = ((Litex.integerDivisionValue (M := M) true) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) (M.number (6 : ℂ))) (M.number (3 : ℂ))) from by
          have _litex_residual : ((Litex.integerDivisionValue (M := M) true) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) (M.number (6 : ℂ))) (M.number (3 : ℂ))) = ((Litex.integerDivisionValue (M := M) true) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) (M.number (6 : ℂ))) (M.number (3 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (6 : ℂ)), (M.number (3 : ℂ))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i11 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (6 : ℂ)), (M.number (3 : ℂ))])) = ((Litex.integerDivisionValue (M := M) true) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) (M.number (6 : ℂ))) (M.number (3 : ℂ))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i11 (M := M));
        let _wd_1_1 := (Litex.number (M := M) (6 : ℂ));
        let _wd_1_2 := (Litex.number (M := M) (3 : ℂ));
        (let _litex_call_arg_0 := _wd_1_1;
        let _litex_call_arg_1 := _wd_1_2;
        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.Z (M := M))), (Litex.denote (Litex.NPos (M := M)))] (by
          have _finiteProof_0 := (Litex.isSet (Litex.Z (M := M)))
          have _finiteProof_1 := (Litex.isSet (Litex.NPos (M := M)))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )) (Litex.Z (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i12 : M.Value) (_raw_i13 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _wd_1_0 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.formulaFnInFnSet _wd_1_0) (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (Litex.NativeBridge.numberInZOfEq (M := M) (6 : ℂ) (6 : ℤ) (by norm_num)) (Litex.numberInNPosOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num) (by norm_num))) True.intro))
          have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_498 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
          exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i12 : M.Value) (_raw_i13 : M.Value) => ((Litex.integerDivisionValue (M := M) true) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) _raw_i12) _raw_i13)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = ((Litex.integerDivisionValue (M := M) true) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) (M.number (6 : ℂ))) (M.number (3 : ℂ))); exact (congrArg₂ (fun (_raw_i12 : M.Value) (_raw_i13 : M.Value) => ((Litex.integerDivisionValue (M := M) true) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) _raw_i12) _raw_i13)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(M.number (6 : ℂ)), (M.number (3 : ℂ))]) (M.number (1 : ℂ)) = (M.number (6 : ℂ)) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(M.number (6 : ℂ)), (M.number (3 : ℂ))] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(M.number (6 : ℂ)), (M.number (3 : ℂ))]) (M.number (2 : ℂ)) = (M.number (3 : ℂ)) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(M.number (6 : ℂ)), (M.number (3 : ℂ))] (1 : Fin 2)))))
        ))).trans _litex_residual)))
      )
  )

noncomputable def _object_w48 := ((_object_w47 (M := M))).val.left

theorem h_1544 : (by
  let _equal_wd_1_0 := (_object_w48 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (7 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w48 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (7 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) (M.number (6 : ℂ))) = (M.number (7 : ℂ)) from by
          have _litex_residual : (M.addValue (M.number (6 : ℂ)) (M.number (1 : ℂ))) = (M.number (7 : ℂ)) := (let _equal_wd_2_0 := (Litex.add (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (7 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (7 : ℂ)) ((6 : ℂ) + (1 : ℂ)) (7 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ)) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) (M.number (6 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) (M.number (6 : ℂ))) = (M.addValue (M.number (6 : ℂ)) (M.number (1 : ℂ))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i9 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (6 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (6 : ℂ) (6 : ℤ) (by norm_num)) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_286 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) (fun (_raw_i10 : M.Value) => (M.addValue _raw_i10 (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i10 : M.Value) => (M.addValue _raw_i10 (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (M.number (6 : ℂ)) (M.number (1 : ℂ))) from rfl))
        ))).trans _litex_residual)))
      )
  )

noncomputable def _object_w50 := (Litex.quot (Litex.number (M := M) (7 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (7 : ℂ) (7 : ℤ) (by norm_num)) (Litex.numberInNPosOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num) (by norm_num)))

theorem h_1620 : (by
  let _equal_wd_1_0 := (_object_w47 (M := M))
  let _equal_wd_1_1 := (_object_w50 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (congrArg₂ (Litex.integerDivisionValue (M := M) true) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) (M.number (6 : ℂ))) = (M.number (7 : ℂ)) from (h_1544 (M := M))) (show (M.number (3 : ℂ)) = (M.number (3 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)))
      )
  )

theorem h_1646 : (by
  let _equal_wd_1_0 := (_object_w50 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w50 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (2 : ℂ) (let _intop := (_object_w50 (M := M));
        let _member : Litex.In _intop Litex.C := Litex.integerToComplex _intop (Litex.quotInZ _intop);
        (Litex.quotDenoteInt _intop (7 : ℤ) (3 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))).trans (congrArg M.number (by norm_num : (7 : ℂ) = ((7 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ))).trans (congrArg M.number (by norm_num : (3 : ℂ) = ((3 : ℤ) : ℂ))))).trans (congrArg M.number (by norm_num))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (by norm_num))))
      )
  )

theorem h_1648 : (by
  let _equal_wd_1_0 := (_object_w46 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (2 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (((((h_1213 (M := M))).trans (h_1620 (M := M)))).trans (h_1646 (M := M)))
      )
  )

theorem h_1651 : ∀ {_Host_i14 : Type v14} [_rep_i14 : Litex.Representation M _Host_i14] (_value_i14 : Litex.Obj (M := M) _Host_i14) (h_1654 : Litex.In _value_i14 (Litex.Z (M := M))), (by
  let _equal_wd_1_0 := (let _litex_call_arg_0 := _value_i14;
  let _litex_call_arg_1 := (Litex.number (M := M) (1 : ℂ));
  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_71 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 h_1654 (Litex.numberInNPosOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num) (by norm_num))), True.intro⟩))
  exact Litex.Same _equal_wd_1_0 _value_i14) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i14 _rep_i14 _value_i14 h_1654
          have h_1671 : Litex.In _value_i14 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_1654
                )
            )
          let _object_w53 := (let _litex_call_arg_0 := _value_i14;
          let _litex_call_arg_1 := (Litex.number (M := M) (1 : ℂ));
          Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_71 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 h_1671 (Litex.numberInNPosOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num) (by norm_num))), True.intro⟩))

          let _object_w54 := (Litex.quot _value_i14 (Litex.number (M := M) (1 : ℂ)) h_1671 (Litex.numberInNPosOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num) (by norm_num)))

          have h_1652 : (by
            let _equal_wd_1_0 := _object_w53
            let _equal_wd_1_1 := _object_w54
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w53;
                  let _equal_wd_1_1 := _object_w54;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i14), (M.number (1 : ℂ))])) = ((Litex.integerDivisionValue (M := M) true) (Litex.denote _value_i14) (M.number (1 : ℂ))) from by
                    have _litex_residual : ((Litex.integerDivisionValue (M := M) true) (Litex.denote _value_i14) (M.number (1 : ℂ))) = ((Litex.integerDivisionValue (M := M) true) (Litex.denote _value_i14) (M.number (1 : ℂ))) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i14), (M.number (1 : ℂ))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i14), (M.number (1 : ℂ))])) = ((Litex.integerDivisionValue (M := M) true) (Litex.denote _value_i14) (M.number (1 : ℂ))) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                  let _wd_1_1 := _value_i14;
                  let _wd_1_2 := (Litex.number (M := M) (1 : ℂ));
                  (let _litex_call_arg_0 := _wd_1_1;
                  let _litex_call_arg_1 := _wd_1_2;
                  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.Z (M := M))), (Litex.denote (Litex.NPos (M := M)))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.Z (M := M)))
                    have _finiteProof_1 := (Litex.isSet (Litex.NPos (M := M)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.Z (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _wd_1_0 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.formulaFnInFnSet _wd_1_0) (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 h_1671 (Litex.numberInNPosOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num) (by norm_num))) True.intro))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_72 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => ((Litex.integerDivisionValue (M := M) true) _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = ((Litex.integerDivisionValue (M := M) true) (Litex.denote _value_i14) (M.number (1 : ℂ))); exact (congrArg₂ (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => ((Litex.integerDivisionValue (M := M) true) _raw_i2 _raw_i3)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i14), (M.number (1 : ℂ))]) (M.number (1 : ℂ)) = (Litex.denote _value_i14) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i14), (M.number (1 : ℂ))] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i14), (M.number (1 : ℂ))]) (M.number (2 : ℂ)) = (M.number (1 : ℂ)) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i14), (M.number (1 : ℂ))] (1 : Fin 2)))))
                  ))).trans _litex_residual)))
                )
            )
          have h_1653 : (by
            let _equal_wd_1_0 := _object_w54
            exact Litex.Same _equal_wd_1_0 _value_i14) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w54;
                  (show Litex.Same _equal_wd_1_0 _value_i14 from (by
                    let _quot := _equal_wd_1_0
                    exact (Litex.quotByOne _quot (Litex.sameRefl (Litex.number (M := M) 1)))
                  )))
                )
            )
          exact ((h_1652).trans h_1653)
        )
      )
  )

theorem h_1834 : (by
  have h_1835 : (by
    let _atomic_wd_1_0 := ((_object_w44 (M := M))).val.first
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := ((_object_w44 (M := M))).val.first
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (7 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (7 : ℂ)) (-7 : ℤ) (by norm_num))))
        )
    )
  exact (by
    let _equal_wd_1_0 := (let _wd_1_0 := ((_object_w44 (M := M))).val.first;
    let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
    (let _litex_call_arg_0 := _wd_1_0;
    let _litex_call_arg_1 := _wd_1_1;
    Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_71 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact h_1835) (Litex.numberInNPosOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num) (by norm_num))), True.intro⟩)))
    let _equal_wd_1_1 := ((_object_w44 (M := M))).val.first
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_1835 : (by
            let _atomic_wd_1_0 := ((_object_w44 (M := M))).val.first
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := ((_object_w44 (M := M))).val.first
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (7 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (7 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (7 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (7 : ℂ)) (-7 : ℤ) (by norm_num))))
                )
            )
          have h_1836 : Litex.Same (let _wd_1_0 := ((_object_w44 (M := M))).val.first;
          let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
          (let _litex_call_arg_0 := _wd_1_0;
          let _litex_call_arg_1 := _wd_1_1;
          Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_71 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact h_1835) (Litex.numberInNPosOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num) (by norm_num))), True.intro⟩))) ((_object_w44 (M := M))).val.first :=
            (by
              litex_checked_step =>
                exact (
                  ((h_1651 (M := M)) ((_object_w44 (M := M))).val.first h_1835)
                )
            )
          exact (let _equal_wd_1_0 := (let _wd_1_0 := ((_object_w44 (M := M))).val.first;
        let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
        (let _litex_call_arg_0 := _wd_1_0;
        let _litex_call_arg_1 := _wd_1_1;
        Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_71 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact h_1835) (Litex.numberInNPosOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num) (by norm_num))), True.intro⟩)));
        let _equal_wd_1_1 := ((_object_w44 (M := M))).val.first;
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((Litex.sameRefl _equal_wd_1_0)).symm.trans ((h_1836).trans (Litex.sameRefl _equal_wd_1_1)))))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_integer_x5f_division_x5f_functions_x2f_statement_x2e_lit
