import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_gcd_x5f_lcm_x5f_functions_x2f_statement_x2e_lit

universe u v7
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFnOn (let _litex_output := (Litex.NPos (M := M)); Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.Z (M := M))), (Litex.denote (Litex.Z (M := M)))]) (Litex.denote _litex_output) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.Z (M := M))), (Litex.denote (Litex.Z (M := M)))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.Z (M := M)))
  have _finiteProof_1 := (Litex.isSet (Litex.Z (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet _litex_output) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∨ ((¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => ((Litex.gcdLcmValue (M := M) false) _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
  have _litex_checked_return : ∀ (_raw_i2 : M.Value) (_raw_i3 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.Z (M := M))) → M.mem _raw_i3 (Litex.denote (Litex.Z (M := M))) → ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∨ ((¬ (_raw_i3 = (M.number (0 : ℂ))))))) _raw_i2 _raw_i3) → M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => ((Litex.gcdLcmValue (M := M) false) _raw_i2 _raw_i3)) _raw_i2 _raw_i3) (Litex.denote (Litex.NPos (M := M))) := (by
    intro _raw_i2 _raw_i3 h_30 h_31 h_3
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_30)
    have h_30 : Litex.In _value_i2 (Litex.Z (M := M)) := h_30
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_31)
    have h_31 : Litex.In _value_i3 (Litex.Z (M := M)) := h_31
    have h_3 : ((¬ Litex.Same _value_i2 (Litex.number (M := M) (0 : ℂ))) ∨ (¬ Litex.Same _value_i3 (Litex.number (M := M) (0 : ℂ)))) :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∨ ((¬ (_raw_i3 = (M.number (0 : ℂ))))))
              exact h_3)
          )
      )
    change (by
      let _atomic_wd_1_0 := (Litex.gcd _value_i2 _value_i3 h_30 h_31 h_3)
      exact Litex.In _atomic_wd_1_0 (Litex.NPos (M := M)))
    exact (by
      let _atomic_wd_1_0 := (Litex.gcd _value_i2 _value_i3 h_30 h_31 h_3)
      exact (Litex.gcdInNPos _atomic_wd_1_0)))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.Z (M := M))), (Litex.denote (Litex.Z (M := M)))]) (Litex.denote (Litex.NPos (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.Z (M := M))), (Litex.denote (Litex.Z (M := M)))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.Z (M := M)))
  have _finiteProof_1 := (Litex.isSet (Litex.Z (M := M)))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet (Litex.NPos (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∨ ((¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
  exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard))
theorem h_1584 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_1585 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_i4 := (Litex.formulaFn2 (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.natural (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => ((Litex.gcdLcmValue (M := M) true) _raw_i5 _raw_i6)) (by
  intro _raw_i5 _raw_i6 h_1612 h_1613 _
  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_1612)
  have h_1612 : Litex.In _value_i5 (Litex.Z (M := M)) := h_1612
  let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_1613)
  have h_1613 : Litex.In _value_i6 (Litex.Z (M := M)) := h_1613
  change (by
    let _atomic_wd_1_0 := (Litex.lcm _value_i5 _value_i6 h_1612 h_1613)
    exact Litex.In _atomic_wd_1_0 (Litex.N (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.lcm _value_i5 _value_i6 h_1612 h_1613)
    exact (Litex.lcmInN _atomic_wd_1_0))))
theorem h_1654 : Litex.In (_object_i4 (M := M)) (Litex.fnSet ((_object_i4 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i4 (M := M)))
      )
  )
theorem h_1655 : Litex.Same (_object_i4 (M := M)) (_object_i4 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i4 (M := M)))
      )
  )

noncomputable def _object_w20 := (let _wd_1_0 := (Litex.number (M := M) (54 : ℂ));
let _object_w13 := (Litex.neg (Litex.number (M := M) (24 : ℂ)) (Litex.numberInC (M := M) (24 : ℂ)));
(let _litex_call_arg_0 := _wd_1_0;
let _litex_call_arg_1 := _object_w13;
Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1584 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (Litex.NativeBridge.numberInZOfEq (M := M) (54 : ℂ) (54 : ℤ) (by norm_num)) (by
  let _atomic_wd_1_0 := _object_w13
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (24 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w13).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (24 : ℂ)) (-24 : ℤ) (by norm_num))))), (Eq.mpr (congrArg₂ (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∨ ((¬ (_raw_i3 = (M.number (0 : ℂ))))))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) (by
  classical
  have _litex_sum_nonzero : (by
  let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.powNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
  let _wd_2_1 := (let _wd_3_0 := _object_w13;
  let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
    let _atomic_wd_2_0 := _object_w13
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w13).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
  (Litex.add _wd_2_0 _wd_2_1 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (2916 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ)))).trans (congrArg M.number (by norm_num : ((54 : ℂ) ^ (2 : ℕ)) = (2916 : ℂ)))) (Litex.numberInC (M := M) (2916 : ℂ)))) (by
    let _atomic_wd_2_0 := _wd_2_1
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (576 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_2_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
      let _atomic_wd_3_0 := _object_w13
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w13).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w13).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (24 : ℂ)) ^ (2 : ℕ)) = (576 : ℂ)))) (Litex.numberInC (M := M) (576 : ℂ))))))
  exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) := (by
  let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.powNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
  let _wd_2_1 := (let _wd_3_0 := _object_w13;
  let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
    let _atomic_wd_2_0 := _object_w13
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w13).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
  (Litex.add _wd_2_0 _wd_2_1 (by
    let _atomic_wd_2_0 := _wd_2_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (2916 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ)))).trans (congrArg M.number (by norm_num : ((54 : ℂ) ^ (2 : ℕ)) = (2916 : ℂ)))) (Litex.numberInC (M := M) (2916 : ℂ)))) (by
    let _atomic_wd_2_0 := _wd_2_1
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (576 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_2_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
      let _atomic_wd_3_0 := _object_w13
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w13).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w13).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (24 : ℂ)) ^ (2 : ℕ)) = (576 : ℂ)))) (Litex.numberInC (M := M) (576 : ℂ))))))
  exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (((54 : ℂ) ^ (2 : ℕ)) + ((- (24 : ℂ)) ^ (2 : ℕ))) (0 : ℂ) (Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ))) (Litex.NativeBridge.denotePowNatReal ((_atomic_wd_1_0).val.right).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
    let _atomic_wd_2_0 := _object_w13
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w13).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w13).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
  by_cases _litex_left : Litex.Same _wd_1_0 (Litex.number (M := M) (0 : ℂ))
  · apply Or.inr
    intro _litex_right
    have _litex_x_zero : (54 : ℂ) = (0 : ℂ) := Litex.NativeBridge.nativeEqOfDenoteNumber _wd_1_0 (Litex.number (M := M) (0 : ℂ)) (54 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (_litex_left)
    have _litex_y_zero : (- (24 : ℂ)) = (0 : ℂ) := Litex.NativeBridge.nativeEqOfDenoteNumber _object_w13 (Litex.number (M := M) (0 : ℂ)) (- (24 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w13).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (_litex_right)
    apply _litex_sum_nonzero
    exact Litex.NativeBridge.sameOfDenoteNumber (let _wd_2_0 := (Litex.powNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
let _wd_2_1 := (let _wd_3_0 := _object_w13;
let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
  let _atomic_wd_1_0 := _object_w13
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w13).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
(Litex.add _wd_2_0 _wd_2_1 (by
  let _atomic_wd_1_0 := _wd_2_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2916 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ)))).trans (congrArg M.number (by norm_num : ((54 : ℂ) ^ (2 : ℕ)) = (2916 : ℂ)))) (Litex.numberInC (M := M) (2916 : ℂ)))) (by
  let _atomic_wd_1_0 := _wd_2_1
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (576 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
    let _atomic_wd_2_0 := _object_w13
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w13).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w13).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (24 : ℂ)) ^ (2 : ℕ)) = (576 : ℂ)))) (Litex.numberInC (M := M) (576 : ℂ)))))) (Litex.number (M := M) (0 : ℂ)) (((54 : ℂ) ^ (2 : ℕ)) + ((- (24 : ℂ)) ^ (2 : ℕ))) (0 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.powNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (let _wd_2_0 := _object_w13;
let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
  let _atomic_wd_1_0 := _object_w13
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w13).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (by
  let _atomic_wd_1_0 := (Litex.powNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2916 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ)))).trans (congrArg M.number (by norm_num : ((54 : ℂ) ^ (2 : ℕ)) = (2916 : ℂ)))) (Litex.numberInC (M := M) (2916 : ℂ)))) (by
  let _atomic_wd_1_0 := (let _wd_2_0 := _object_w13;
  let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
    let _atomic_wd_2_0 := _object_w13
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w13).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (576 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
    let _atomic_wd_2_0 := _object_w13
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w13).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w13).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (24 : ℂ)) ^ (2 : ℕ)) = (576 : ℂ)))) (Litex.numberInC (M := M) (576 : ℂ)))) _ _ (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ))) (Litex.NativeBridge.denotePowNatReal _object_w13 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
  let _atomic_wd_1_0 := _object_w13
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w13).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w13).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) ((congrArg₂ (fun (x y : ℂ) => x ^ (2 : ℕ) + y ^ (2 : ℕ)) _litex_x_zero _litex_y_zero).trans (by norm_num))
  · exact Or.inl _litex_left
))⟩)))

theorem h_1656 : (by
  let _equal_wd_1_0 := (_object_w20 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w20 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (54 : ℂ)), (M.negValue (M.number (24 : ℂ)))])) = (M.number (6 : ℂ)) from by
          have _litex_residual : ((Litex.gcdLcmValue (M := M) false) (M.number (54 : ℂ)) (M.negValue (M.number (24 : ℂ)))) = (M.number (6 : ℂ)) := (let _equal_wd_2_0 := (let _wd_1_0 := (Litex.number (M := M) (54 : ℂ));
          let _wd_1_1 := (_equal_wd_1_0).val.argument.val.second;
          (Litex.gcd _wd_1_0 _wd_1_1 (Litex.NativeBridge.numberInZOfEq (M := M) (54 : ℂ) (54 : ℤ) (by norm_num)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (24 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (24 : ℂ)) (-24 : ℤ) (by norm_num)))) (by
            classical
            have _litex_sum_nonzero : (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.powNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
            let _wd_2_1 := (let _wd_3_0 := _wd_1_1;
            let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
              let _atomic_wd_2_0 := _wd_3_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
            (Litex.add _wd_2_0 _wd_2_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (2916 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ)))).trans (congrArg M.number (by norm_num : ((54 : ℂ) ^ (2 : ℕ)) = (2916 : ℂ)))) (Litex.numberInC (M := M) (2916 : ℂ)))) (by
              let _atomic_wd_2_0 := _wd_2_1
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (576 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_2_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                let _atomic_wd_3_0 := (_atomic_wd_2_0).val.base
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_atomic_wd_3_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) ((_atomic_wd_2_0).val.base).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (24 : ℂ)) ^ (2 : ℕ)) = (576 : ℂ)))) (Litex.numberInC (M := M) (576 : ℂ))))))
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) := (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.powNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
            let _wd_2_1 := (let _wd_3_0 := _wd_1_1;
            let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
              let _atomic_wd_2_0 := _wd_3_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
            (Litex.add _wd_2_0 _wd_2_1 (by
              let _atomic_wd_2_0 := _wd_2_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (2916 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ)))).trans (congrArg M.number (by norm_num : ((54 : ℂ) ^ (2 : ℕ)) = (2916 : ℂ)))) (Litex.numberInC (M := M) (2916 : ℂ)))) (by
              let _atomic_wd_2_0 := _wd_2_1
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (576 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_2_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                let _atomic_wd_3_0 := (_atomic_wd_2_0).val.base
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_atomic_wd_3_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) ((_atomic_wd_2_0).val.base).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (24 : ℂ)) ^ (2 : ℕ)) = (576 : ℂ)))) (Litex.numberInC (M := M) (576 : ℂ))))))
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (((54 : ℂ) ^ (2 : ℕ)) + ((- (24 : ℂ)) ^ (2 : ℕ))) (0 : ℂ) (Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ))) (Litex.NativeBridge.denotePowNatReal ((_atomic_wd_1_0).val.right).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
              let _atomic_wd_2_0 := ((_atomic_wd_1_0).val.right).val.base
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (((_atomic_wd_1_0).val.right).val.base).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            by_cases _litex_left : Litex.Same _wd_1_0 (Litex.number (M := M) (0 : ℂ))
            · apply Or.inr
              intro _litex_right
              have _litex_x_zero : (54 : ℂ) = (0 : ℂ) := Litex.NativeBridge.nativeEqOfDenoteNumber _wd_1_0 (Litex.number (M := M) (0 : ℂ)) (54 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (_litex_left)
              have _litex_y_zero : (- (24 : ℂ)) = (0 : ℂ) := Litex.NativeBridge.nativeEqOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (- (24 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (Litex.numberInC (M := M) (24 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (_litex_right)
              apply _litex_sum_nonzero
              exact Litex.NativeBridge.sameOfDenoteNumber (let _wd_2_0 := (Litex.powNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
          let _wd_2_1 := (let _wd_3_0 := _wd_1_1;
          let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_3_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          (Litex.add _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2916 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ)))).trans (congrArg M.number (by norm_num : ((54 : ℂ) ^ (2 : ℕ)) = (2916 : ℂ)))) (Litex.numberInC (M := M) (2916 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_2_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (576 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
              let _atomic_wd_2_0 := (_atomic_wd_1_0).val.base
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) ((_atomic_wd_1_0).val.base).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (24 : ℂ)) ^ (2 : ℕ)) = (576 : ℂ)))) (Litex.numberInC (M := M) (576 : ℂ)))))) (Litex.number (M := M) (0 : ℂ)) (((54 : ℂ) ^ (2 : ℕ)) + ((- (24 : ℂ)) ^ (2 : ℕ))) (0 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.powNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (let _wd_2_0 := _wd_1_1;
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (by
            let _atomic_wd_1_0 := (Litex.powNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2916 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ)))).trans (congrArg M.number (by norm_num : ((54 : ℂ) ^ (2 : ℕ)) = (2916 : ℂ)))) (Litex.numberInC (M := M) (2916 : ℂ)))) (by
            let _atomic_wd_1_0 := (let _wd_2_0 := _wd_1_1;
            let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
              let _atomic_wd_2_0 := _wd_2_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (576 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
              let _atomic_wd_2_0 := (_atomic_wd_1_0).val.base
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_atomic_wd_2_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) ((_atomic_wd_1_0).val.base).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (24 : ℂ)) ^ (2 : ℕ)) = (576 : ℂ)))) (Litex.numberInC (M := M) (576 : ℂ)))) _ _ (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ))) (Litex.NativeBridge.denotePowNatReal _wd_1_1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (Litex.numberInC (M := M) (24 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) ((congrArg₂ (fun (x y : ℂ) => x ^ (2 : ℕ) + y ^ (2 : ℕ)) _litex_x_zero _litex_y_zero).trans (by norm_num))
            · exact Or.inl _litex_left
          )));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (6 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (6 : ℂ)) (6 : ℂ) (6 : ℂ) (let _intop := _equal_wd_2_0;
          let _member : Litex.In _intop Litex.C := Litex.naturalToComplex _intop (Litex.gcdInN _intop);
          (Litex.gcdDenoteInt _intop (54 : ℤ) (-24 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ))).trans (congrArg M.number (by norm_num : (54 : ℂ) = ((54 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) ((_equal_wd_2_0).val.right).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ)))).trans (congrArg M.number (by norm_num : (- (24 : ℂ)) = ((-24 : ℤ) : ℂ))))).trans (congrArg M.number (by norm_num [Int.gcd_eq_natAbs_gcd_natAbs]))) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (54 : ℂ)), (M.negValue (M.number (24 : ℂ)))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (54 : ℂ)), (M.negValue (M.number (24 : ℂ)))])) = ((Litex.gcdLcmValue (M := M) false) (M.number (54 : ℂ)) (M.negValue (M.number (24 : ℂ)))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
        let _wd_1_1 := (Litex.number (M := M) (54 : ℂ));
        let _object_w19 := (_equal_wd_1_0).val.argument.val.second;
        (let _litex_call_arg_0 := _wd_1_1;
        let _litex_call_arg_1 := _object_w19;
        Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.Z (M := M))), (Litex.denote (Litex.Z (M := M)))] (by
          have _finiteProof_0 := (Litex.isSet (Litex.Z (M := M)))
          have _finiteProof_1 := (Litex.isSet (Litex.Z (M := M)))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )) (Litex.NPos (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∨ ((¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _wd_1_0 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.formulaFnInFnSet _wd_1_0) (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (Litex.NativeBridge.numberInZOfEq (M := M) (54 : ℂ) (54 : ℤ) (by norm_num)) (by
          let _atomic_wd_1_0 := _object_w19
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (24 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w19).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (24 : ℂ)) (-24 : ℤ) (by norm_num))))) (Eq.mpr (congrArg₂ (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∨ ((¬ (_raw_i3 = (M.number (0 : ℂ))))))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) (by
          classical
          have _litex_sum_nonzero : (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.powNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
          let _wd_2_1 := (let _wd_3_0 := _object_w19;
          let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
            let _atomic_wd_2_0 := _object_w19
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w19).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          (Litex.add _wd_2_0 _wd_2_1 (by
            let _atomic_wd_2_0 := _wd_2_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (2916 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ)))).trans (congrArg M.number (by norm_num : ((54 : ℂ) ^ (2 : ℕ)) = (2916 : ℂ)))) (Litex.numberInC (M := M) (2916 : ℂ)))) (by
            let _atomic_wd_2_0 := _wd_2_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (576 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_2_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
              let _atomic_wd_3_0 := _object_w19
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w19).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w19).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (24 : ℂ)) ^ (2 : ℕ)) = (576 : ℂ)))) (Litex.numberInC (M := M) (576 : ℂ))))))
          exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) := (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.powNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
          let _wd_2_1 := (let _wd_3_0 := _object_w19;
          let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
            let _atomic_wd_2_0 := _object_w19
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w19).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          (Litex.add _wd_2_0 _wd_2_1 (by
            let _atomic_wd_2_0 := _wd_2_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (2916 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ)))).trans (congrArg M.number (by norm_num : ((54 : ℂ) ^ (2 : ℕ)) = (2916 : ℂ)))) (Litex.numberInC (M := M) (2916 : ℂ)))) (by
            let _atomic_wd_2_0 := _wd_2_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (576 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_2_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
              let _atomic_wd_3_0 := _object_w19
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w19).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w19).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (24 : ℂ)) ^ (2 : ℕ)) = (576 : ℂ)))) (Litex.numberInC (M := M) (576 : ℂ))))))
          exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (((54 : ℂ) ^ (2 : ℕ)) + ((- (24 : ℂ)) ^ (2 : ℕ))) (0 : ℂ) (Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ))) (Litex.NativeBridge.denotePowNatReal ((_atomic_wd_1_0).val.right).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
            let _atomic_wd_2_0 := _object_w19
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w19).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w19).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
          by_cases _litex_left : Litex.Same _wd_1_1 (Litex.number (M := M) (0 : ℂ))
          · apply Or.inr
            intro _litex_right
            have _litex_x_zero : (54 : ℂ) = (0 : ℂ) := Litex.NativeBridge.nativeEqOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (54 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (_litex_left)
            have _litex_y_zero : (- (24 : ℂ)) = (0 : ℂ) := Litex.NativeBridge.nativeEqOfDenoteNumber _object_w19 (Litex.number (M := M) (0 : ℂ)) (- (24 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w19).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (_litex_right)
            apply _litex_sum_nonzero
            exact Litex.NativeBridge.sameOfDenoteNumber (let _wd_2_0 := (Litex.powNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
        let _wd_2_1 := (let _wd_3_0 := _object_w19;
        let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
          let _atomic_wd_1_0 := _object_w19
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w19).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
        (Litex.add _wd_2_0 _wd_2_1 (by
          let _atomic_wd_1_0 := _wd_2_0
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2916 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ)))).trans (congrArg M.number (by norm_num : ((54 : ℂ) ^ (2 : ℕ)) = (2916 : ℂ)))) (Litex.numberInC (M := M) (2916 : ℂ)))) (by
          let _atomic_wd_1_0 := _wd_2_1
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (576 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
            let _atomic_wd_2_0 := _object_w19
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w19).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w19).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (24 : ℂ)) ^ (2 : ℕ)) = (576 : ℂ)))) (Litex.numberInC (M := M) (576 : ℂ)))))) (Litex.number (M := M) (0 : ℂ)) (((54 : ℂ) ^ (2 : ℕ)) + ((- (24 : ℂ)) ^ (2 : ℕ))) (0 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.powNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (let _wd_2_0 := _object_w19;
        let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
          let _atomic_wd_1_0 := _object_w19
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w19).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (by
          let _atomic_wd_1_0 := (Litex.powNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (2916 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ)))).trans (congrArg M.number (by norm_num : ((54 : ℂ) ^ (2 : ℕ)) = (2916 : ℂ)))) (Litex.numberInC (M := M) (2916 : ℂ)))) (by
          let _atomic_wd_1_0 := (let _wd_2_0 := _object_w19;
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_2_0 := _object_w19
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w19).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (576 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
            let _atomic_wd_2_0 := _object_w19
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w19).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w19).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (24 : ℂ)) ^ (2 : ℕ)) = (576 : ℂ)))) (Litex.numberInC (M := M) (576 : ℂ)))) _ _ (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (54 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (54 : ℂ) (54 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (54 : ℂ))) (Litex.NativeBridge.denotePowNatReal _object_w19 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
          let _atomic_wd_1_0 := _object_w19
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (24 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w19).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (24 : ℂ)) (-24 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (24 : ℂ)) (_object_w19).wd _ (Litex.NativeBridge.denoteNumber (M := M) (24 : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) ((congrArg₂ (fun (x y : ℂ) => x ^ (2 : ℕ) + y ^ (2 : ℕ)) _litex_x_zero _litex_y_zero).trans (by norm_num))
          · exact Or.inl _litex_left
        ))))
          have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_1585 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
          exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => ((Litex.gcdLcmValue (M := M) false) _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = ((Litex.gcdLcmValue (M := M) false) (M.number (54 : ℂ)) (M.negValue (M.number (24 : ℂ)))); exact (congrArg₂ (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => ((Litex.gcdLcmValue (M := M) false) _raw_i2 _raw_i3)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(M.number (54 : ℂ)), (M.negValue (M.number (24 : ℂ)))]) (M.number (1 : ℂ)) = (M.number (54 : ℂ)) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(M.number (54 : ℂ)), (M.negValue (M.number (24 : ℂ)))] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(M.number (54 : ℂ)), (M.negValue (M.number (24 : ℂ)))]) (M.number (2 : ℂ)) = (M.negValue (M.number (24 : ℂ))) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(M.number (54 : ℂ)), (M.negValue (M.number (24 : ℂ)))] (1 : Fin 2)))))
        ))).trans _litex_residual)))
      )
  )

noncomputable def _object_w27 := (let _object_w22 := (Litex.neg (Litex.number (M := M) (6 : ℂ)) (Litex.numberInC (M := M) (6 : ℂ)));
let _wd_1_1 := (Litex.number (M := M) (15 : ℂ));
(Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.natural (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (_object_i4 (M := M)) _object_w22 _wd_1_1 (h_1654 (M := M)) (by
  let _atomic_wd_1_0 := _object_w22
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (6 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (6 : ℂ)) (_object_w22).wd _ (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (6 : ℂ)) (-6 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (15 : ℂ) (15 : ℤ) (by norm_num)) True.intro))

theorem h_2013 : (by
  let _equal_wd_1_0 := (_object_w27 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (30 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w27 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (30 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.negValue (M.number (6 : ℂ))), (M.number (15 : ℂ))])) = (M.number (30 : ℂ)) from by
          have _litex_residual : ((Litex.gcdLcmValue (M := M) true) (M.negValue (M.number (6 : ℂ))) (M.number (15 : ℂ))) = (M.number (30 : ℂ)) := (let _equal_wd_2_0 := (let _wd_1_0 := (_equal_wd_1_0).val.first;
          let _wd_1_1 := (Litex.number (M := M) (15 : ℂ));
          (Litex.lcm _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (6 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (6 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (6 : ℂ)) (-6 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (15 : ℂ) (15 : ℤ) (by norm_num))));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (30 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (30 : ℂ)) (30 : ℂ) (30 : ℂ) (let _intop := _equal_wd_2_0;
          let _member : Litex.In _intop Litex.C := Litex.naturalToComplex _intop (Litex.lcmInN _intop);
          (Litex.lcmDenoteInt _intop (-6 : ℤ) (15 : ℤ) (((Litex.NativeBridge.denoteNeg (Litex.number (M := M) (6 : ℂ)) ((_equal_wd_2_0).val.left).wd _ (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)))).trans (congrArg M.number (by norm_num : (- (6 : ℂ)) = ((-6 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (15 : ℂ))).trans (congrArg M.number (by norm_num : (15 : ℂ) = ((15 : ℤ) : ℂ))))).trans (congrArg M.number (by norm_num [Int.lcm_eq_natAbs_lcm_natAbs]))) (Litex.NativeBridge.denoteNumber (M := M) (30 : ℂ)) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.negValue (M.number (6 : ℂ))), (M.number (15 : ℂ))])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i4 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(M.negValue (M.number (6 : ℂ))), (M.number (15 : ℂ))])) = ((Litex.gcdLcmValue (M := M) true) (M.negValue (M.number (6 : ℂ))) (M.number (15 : ℂ))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i4 (M := M));
          let _object_w26 := (_equal_wd_1_0).val.first;
          let _wd_1_2 := (Litex.number (M := M) (15 : ℂ));
          (Litex.call2 Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.natural (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _wd_1_0 _object_w26 _wd_1_2 (Litex.formulaFnInFnSet _wd_1_0) (by
            let _atomic_wd_1_0 := _object_w26
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (6 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (6 : ℂ)) (_object_w26).wd _ (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (6 : ℂ)) (-6 : ℤ) (by norm_num)))) (Litex.NativeBridge.numberInZOfEq (M := M) (15 : ℂ) (15 : ℤ) (by norm_num)) True.intro))
          have _litex_call_eq := Litex.call2Congr _litex_original _litex_literal (h_1655 (M := M)) (Litex.sameRefl _litex_original.val.first) (Litex.sameRefl _litex_original.val.second)
          have _litex_beta := Litex.callFormula2_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.natural (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => ((Litex.gcdLcmValue (M := M) true) _raw_i5 _raw_i6)) (by intro _x _y _hx _hy _hg; have _h := _litex_literal.val.function.wd (Litex.FiniteFunction.pack2 (M := M) _x _y) ((Litex.FunctionSignature.two_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer Litex.StandardSetValue.natural (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => True) _x _y).mpr ⟨_hx, _hy, _hg⟩); change M.mem ((fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => ((Litex.gcdLcmValue (M := M) true) _raw_i5 _raw_i6)) (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).1 (Litex.FiniteFunction.unpack2 (M := M) (Litex.FiniteFunction.pack2 (M := M) _x _y)).2) (M.standard Litex.StandardSetValue.natural) at _h; simpa only [Litex.FiniteFunction.unpack_pack2] using _h) _litex_literal.val.first _litex_literal.val.second _litex_literal.wd.2.1 _litex_literal.wd.2.2.1 _litex_literal.wd.2.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i5 : M.Value) (_raw_i6 : M.Value) => ((Litex.gcdLcmValue (M := M) true) _raw_i5 _raw_i6)) (Litex.denote _litex_literal.val.first) (Litex.denote _litex_literal.val.second) = ((Litex.gcdLcmValue (M := M) true) (M.negValue (M.number (6 : ℂ))) (M.number (15 : ℂ))) from rfl))
        ))).trans _litex_residual)))
      )
  )

theorem h_2123 : ∀ {_Host_i7 : Type v7} [_rep_i7 : Litex.Representation M _Host_i7] (_value_i7 : Litex.Obj (M := M) _Host_i7) (h_2126 : Litex.In _value_i7 (Litex.Z (M := M))) (h_2121 : ¬ Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ))), (by
  let _equal_wd_1_0 := (let _litex_call_arg_0 := _value_i7;
  let _litex_call_arg_1 := _value_i7;
  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1584 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 h_2126 h_2126), (Eq.mpr (congrArg₂ (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∨ ((¬ (_raw_i3 = (M.number (0 : ℂ))))))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) (by
    classical
    apply Classical.byContradiction
    intro _negative_disjunction
    have h_2952 : Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
      (by
        litex_checked_step =>
          exact (
            (Classical.byContradiction (fun _branch => _negative_disjunction (Or.inr _branch)))
          )
      )
    exact _negative_disjunction (Or.inl h_2121)
  ))⟩))
  let _equal_wd_1_1 := (Litex.abs _value_i7 (Litex.integerToReal _value_i7 h_2126))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i7 _rep_i7 _value_i7 h_2126 h_2121
          have h_2976 : Litex.In _value_i7 (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  h_2126
                )
            )
          let _object_w33 := (let _litex_call_arg_0 := _value_i7;
          let _litex_call_arg_1 := _value_i7;
          Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1584 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 h_2976 h_2976), (Eq.mpr (congrArg₂ (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∨ ((¬ (_raw_i3 = (M.number (0 : ℂ))))))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) (by
            classical
            apply Classical.byContradiction
            intro _negative_disjunction
            have h_3802 : Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Classical.byContradiction (fun _branch => _negative_disjunction (Or.inr _branch)))
                  )
              )
            exact _negative_disjunction (Or.inl h_2121)
          ))⟩))

          let _object_w34 := (Litex.gcd _value_i7 _value_i7 h_2976 h_2976 (by
            classical
            apply Classical.byContradiction
            intro _negative_disjunction
            have h_4632 : Litex.Same _value_i7 (Litex.number (M := M) (0 : ℂ)) :=
              (by
                litex_checked_step =>
                  exact (
                    (Classical.byContradiction (fun _branch => _negative_disjunction (Or.inr _branch)))
                  )
              )
            exact _negative_disjunction (Or.inl h_2121)
          ))

          have h_2124 : (by
            let _equal_wd_1_0 := _object_w33
            let _equal_wd_1_1 := _object_w34
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w33;
                  let _equal_wd_1_1 := _object_w34;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i7)])) = ((Litex.gcdLcmValue (M := M) false) (Litex.denote _value_i7) (Litex.denote _value_i7)) from by
                    have _litex_residual : ((Litex.gcdLcmValue (M := M) false) (Litex.denote _value_i7) (Litex.denote _value_i7)) = ((Litex.gcdLcmValue (M := M) false) (Litex.denote _value_i7) (Litex.denote _value_i7)) := (show @Eq M.Value _ _ from Eq.refl _)
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i7)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i7), (Litex.denote _value_i7)])) = ((Litex.gcdLcmValue (M := M) false) (Litex.denote _value_i7) (Litex.denote _value_i7)) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                  let _wd_1_1 := _value_i7;
                  let _wd_1_2 := _wd_1_1;
                  (let _litex_call_arg_0 := _wd_1_1;
                  let _litex_call_arg_1 := _wd_1_2;
                  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.Z (M := M))), (Litex.denote (Litex.Z (M := M)))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.Z (M := M)))
                    have _finiteProof_1 := (Litex.isSet (Litex.Z (M := M)))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.NPos (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∨ ((¬ (_raw_i3 = (M.number (0 : ℂ))))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _wd_1_0 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.formulaFnInFnSet _wd_1_0) (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 h_2976 h_2976) (Eq.mpr (congrArg₂ (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∨ ((¬ (_raw_i3 = (M.number (0 : ℂ))))))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) (by
                    classical
                    apply Classical.byContradiction
                    intro _negative_disjunction
                    have h_6346 : Litex.Same _wd_1_2 (Litex.number (M := M) (0 : ℂ)) :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Classical.byContradiction (fun _branch => _negative_disjunction (Or.inr _branch)))
                          )
                      )
                    exact _negative_disjunction (Or.inl h_2121)
                  ))))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_1585 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => ((Litex.gcdLcmValue (M := M) false) _raw_i2 _raw_i3)) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = ((Litex.gcdLcmValue (M := M) false) (Litex.denote _value_i7) (Litex.denote _value_i7)); exact (congrArg₂ (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => ((Litex.gcdLcmValue (M := M) false) _raw_i2 _raw_i3)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i7), (Litex.denote _value_i7)]) (M.number (1 : ℂ)) = (Litex.denote _value_i7) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i7), (Litex.denote _value_i7)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i7), (Litex.denote _value_i7)]) (M.number (2 : ℂ)) = (Litex.denote _value_i7) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i7), (Litex.denote _value_i7)] (1 : Fin 2)))))
                  ))).trans _litex_residual)))
                )
            )
          let _object_w35 := (Litex.abs _value_i7 (Litex.integerToReal _value_i7 h_2976))

          have h_2125 : (by
            let _equal_wd_1_0 := _object_w34
            let _equal_wd_1_1 := _object_w35
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w34;
                  let _equal_wd_1_1 := _object_w35;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
                    let _intop := _equal_wd_1_0
                    exact (Litex.gcdSelfAbs _intop (Litex.sameRefl _intop.val.left))
                  )))
                )
            )
          exact ((h_2124).trans h_2125)
        )
      )
  )

theorem h_8887 : (by
  have h_8888 : (by
    let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) :=
    (by
      litex_checked_step =>
        exact (
          (by
            let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (9 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (9 : ℂ)) (-9 : ℤ) (by norm_num))))
        )
    )
  exact (by
    let _equal_wd_1_0 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)));
    let _wd_1_1 := _wd_1_0;
    (let _litex_call_arg_0 := _wd_1_0;
    let _litex_call_arg_1 := _wd_1_1;
    Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1584 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
      let _atomic_wd_1_0 := _wd_1_1
      exact h_8888) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact h_8888)), (Eq.mpr (congrArg₂ (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∨ ((¬ (_raw_i3 = (M.number (0 : ℂ))))))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) (by
      classical
      have _litex_sum_nonzero : (by
      let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := _wd_1_1;
      let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
      (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
        let _atomic_wd_2_0 := _wd_3_0
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
      let _wd_2_1 := _wd_2_0;
      (Litex.add _wd_2_0 _wd_2_1 (by
        let _atomic_wd_2_0 := _wd_2_1
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (81 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_2_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
          let _atomic_wd_3_0 := (_atomic_wd_2_0).val.base
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (9 : ℂ)) ^ (2 : ℕ)) = (81 : ℂ)))) (Litex.numberInC (M := M) (81 : ℂ)))) (by
        let _atomic_wd_2_0 := _wd_2_1
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (81 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_2_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
          let _atomic_wd_3_0 := (_atomic_wd_2_0).val.base
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (9 : ℂ)) ^ (2 : ℕ)) = (81 : ℂ)))) (Litex.numberInC (M := M) (81 : ℂ))))))
      exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) := (by
      let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := _wd_1_1;
      let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
      (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
        let _atomic_wd_2_0 := _wd_3_0
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
      let _wd_2_1 := _wd_2_0;
      (Litex.add _wd_2_0 _wd_2_1 (by
        let _atomic_wd_2_0 := _wd_2_1
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (81 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_2_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
          let _atomic_wd_3_0 := (_atomic_wd_2_0).val.base
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (9 : ℂ)) ^ (2 : ℕ)) = (81 : ℂ)))) (Litex.numberInC (M := M) (81 : ℂ)))) (by
        let _atomic_wd_2_0 := _wd_2_1
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (81 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_2_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
          let _atomic_wd_3_0 := (_atomic_wd_2_0).val.base
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (9 : ℂ)) ^ (2 : ℕ)) = (81 : ℂ)))) (Litex.numberInC (M := M) (81 : ℂ))))))
      exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (((- (9 : ℂ)) ^ (2 : ℕ)) + ((- (9 : ℂ)) ^ (2 : ℕ))) (0 : ℂ) (Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal ((_atomic_wd_1_0).val.left).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
        let _atomic_wd_2_0 := ((_atomic_wd_1_0).val.left).val.base
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ)))) (Litex.NativeBridge.denotePowNatReal ((_atomic_wd_1_0).val.right).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
        let _atomic_wd_2_0 := ((_atomic_wd_1_0).val.left).val.base
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
      by_cases _litex_left : Litex.Same _wd_1_1 (Litex.number (M := M) (0 : ℂ))
      · apply Or.inr
        intro _litex_right
        have _litex_x_zero : (- (9 : ℂ)) = (0 : ℂ) := Litex.NativeBridge.nativeEqOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (- (9 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (_litex_left)
        have _litex_y_zero : (- (9 : ℂ)) = (0 : ℂ) := Litex.NativeBridge.nativeEqOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (- (9 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (_litex_right)
        apply _litex_sum_nonzero
        exact Litex.NativeBridge.sameOfDenoteNumber (let _wd_2_0 := (let _wd_3_0 := _wd_1_1;
    let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
      let _atomic_wd_1_0 := _wd_3_0
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
    let _wd_2_1 := _wd_2_0;
    (Litex.add _wd_2_0 _wd_2_1 (by
      let _atomic_wd_1_0 := _wd_2_1
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (81 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
        let _atomic_wd_2_0 := (_atomic_wd_1_0).val.base
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (9 : ℂ)) ^ (2 : ℕ)) = (81 : ℂ)))) (Litex.numberInC (M := M) (81 : ℂ)))) (by
      let _atomic_wd_1_0 := _wd_2_1
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (81 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
        let _atomic_wd_2_0 := (_atomic_wd_1_0).val.base
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (9 : ℂ)) ^ (2 : ℕ)) = (81 : ℂ)))) (Litex.numberInC (M := M) (81 : ℂ)))))) (Litex.number (M := M) (0 : ℂ)) (((- (9 : ℂ)) ^ (2 : ℕ)) + ((- (9 : ℂ)) ^ (2 : ℕ))) (0 : ℂ) (Litex.NativeBridge.denoteAdd (let _wd_2_0 := _wd_1_1;
    let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
      let _atomic_wd_1_0 := _wd_2_0
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (let _wd_2_0 := _wd_1_1;
    let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
      let _atomic_wd_1_0 := _wd_2_0
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (by
      let _atomic_wd_1_0 := (let _wd_2_0 := _wd_1_1;
      let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
      (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
        let _atomic_wd_2_0 := _wd_2_0
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (81 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
        let _atomic_wd_2_0 := (_atomic_wd_1_0).val.base
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (9 : ℂ)) ^ (2 : ℕ)) = (81 : ℂ)))) (Litex.numberInC (M := M) (81 : ℂ)))) (by
      let _atomic_wd_1_0 := (let _wd_2_0 := _wd_1_1;
      let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
      (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
        let _atomic_wd_2_0 := _wd_2_0
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (81 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
        let _atomic_wd_2_0 := (_atomic_wd_1_0).val.base
        exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (9 : ℂ)) ^ (2 : ℕ)) = (81 : ℂ)))) (Litex.numberInC (M := M) (81 : ℂ)))) _ _ (Litex.NativeBridge.denotePowNatReal _wd_1_1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ)))) (Litex.NativeBridge.denotePowNatReal _wd_1_1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
      let _atomic_wd_1_0 := _wd_1_1
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) ((congrArg₂ (fun (x y : ℂ) => x ^ (2 : ℕ) + y ^ (2 : ℕ)) _litex_x_zero _litex_y_zero).trans (by norm_num))
      · exact Or.inl _litex_left
    ))⟩)))
    let _equal_wd_1_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)));
    (Litex.abs _wd_1_0 (by
      let _atomic_wd_1_0 := _wd_1_0
      exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num))))))
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_8888 : (by
            let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)))
            exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)))
                    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (9 : ℂ)) (Litex.Z (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (_atomic_wd_1_0).wd _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInZOfEq (- (9 : ℂ)) (-9 : ℤ) (by norm_num))))
                )
            )
          have h_8889 : (by
            let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)))
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_0 := (Litex.neg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)))
                    exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (- (9 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
                )
            )
          have h_8890 : Litex.Same (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)));
          let _wd_1_1 := _wd_1_0;
          (let _litex_call_arg_0 := _wd_1_0;
          let _litex_call_arg_1 := _wd_1_1;
          Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1584 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_0 := _wd_1_1
            exact h_8888) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact h_8888)), (Eq.mpr (congrArg₂ (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∨ ((¬ (_raw_i3 = (M.number (0 : ℂ))))))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) (by
            classical
            have _litex_sum_nonzero : (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := _wd_1_1;
            let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
              let _atomic_wd_2_0 := _wd_3_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
            let _wd_2_1 := _wd_2_0;
            (Litex.add _wd_2_0 _wd_2_1 (by
              let _atomic_wd_2_0 := _wd_2_1
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (81 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_2_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                let _atomic_wd_3_0 := (_atomic_wd_2_0).val.base
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (9 : ℂ)) ^ (2 : ℕ)) = (81 : ℂ)))) (Litex.numberInC (M := M) (81 : ℂ)))) (by
              let _atomic_wd_2_0 := _wd_2_1
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (81 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_2_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                let _atomic_wd_3_0 := (_atomic_wd_2_0).val.base
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (9 : ℂ)) ^ (2 : ℕ)) = (81 : ℂ)))) (Litex.numberInC (M := M) (81 : ℂ))))))
            exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) := (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := _wd_1_1;
            let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
              let _atomic_wd_2_0 := _wd_3_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
            let _wd_2_1 := _wd_2_0;
            (Litex.add _wd_2_0 _wd_2_1 (by
              let _atomic_wd_2_0 := _wd_2_1
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (81 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_2_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                let _atomic_wd_3_0 := (_atomic_wd_2_0).val.base
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (9 : ℂ)) ^ (2 : ℕ)) = (81 : ℂ)))) (Litex.numberInC (M := M) (81 : ℂ)))) (by
              let _atomic_wd_2_0 := _wd_2_1
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (81 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_2_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                let _atomic_wd_3_0 := (_atomic_wd_2_0).val.base
                exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (9 : ℂ)) ^ (2 : ℕ)) = (81 : ℂ)))) (Litex.numberInC (M := M) (81 : ℂ))))))
            exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (((- (9 : ℂ)) ^ (2 : ℕ)) + ((- (9 : ℂ)) ^ (2 : ℕ))) (0 : ℂ) (Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal ((_atomic_wd_1_0).val.left).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
              let _atomic_wd_2_0 := ((_atomic_wd_1_0).val.left).val.base
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ)))) (Litex.NativeBridge.denotePowNatReal ((_atomic_wd_1_0).val.right).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
              let _atomic_wd_2_0 := ((_atomic_wd_1_0).val.left).val.base
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
            by_cases _litex_left : Litex.Same _wd_1_1 (Litex.number (M := M) (0 : ℂ))
            · apply Or.inr
              intro _litex_right
              have _litex_x_zero : (- (9 : ℂ)) = (0 : ℂ) := Litex.NativeBridge.nativeEqOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (- (9 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (_litex_left)
              have _litex_y_zero : (- (9 : ℂ)) = (0 : ℂ) := Litex.NativeBridge.nativeEqOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (- (9 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (_litex_right)
              apply _litex_sum_nonzero
              exact Litex.NativeBridge.sameOfDenoteNumber (let _wd_2_0 := (let _wd_3_0 := _wd_1_1;
          let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_3_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          let _wd_2_1 := _wd_2_0;
          (Litex.add _wd_2_0 _wd_2_1 (by
            let _atomic_wd_1_0 := _wd_2_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (81 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
              let _atomic_wd_2_0 := (_atomic_wd_1_0).val.base
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (9 : ℂ)) ^ (2 : ℕ)) = (81 : ℂ)))) (Litex.numberInC (M := M) (81 : ℂ)))) (by
            let _atomic_wd_1_0 := _wd_2_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (81 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
              let _atomic_wd_2_0 := (_atomic_wd_1_0).val.base
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (9 : ℂ)) ^ (2 : ℕ)) = (81 : ℂ)))) (Litex.numberInC (M := M) (81 : ℂ)))))) (Litex.number (M := M) (0 : ℂ)) (((- (9 : ℂ)) ^ (2 : ℕ)) + ((- (9 : ℂ)) ^ (2 : ℕ))) (0 : ℂ) (Litex.NativeBridge.denoteAdd (let _wd_2_0 := _wd_1_1;
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (let _wd_2_0 := _wd_1_1;
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (by
            let _atomic_wd_1_0 := (let _wd_2_0 := _wd_1_1;
            let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
              let _atomic_wd_2_0 := _wd_2_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (81 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
              let _atomic_wd_2_0 := (_atomic_wd_1_0).val.base
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (9 : ℂ)) ^ (2 : ℕ)) = (81 : ℂ)))) (Litex.numberInC (M := M) (81 : ℂ)))) (by
            let _atomic_wd_1_0 := (let _wd_2_0 := _wd_1_1;
            let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
              let _atomic_wd_2_0 := _wd_2_0
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (81 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
              let _atomic_wd_2_0 := (_atomic_wd_1_0).val.base
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (9 : ℂ)) ^ (2 : ℕ)) = (81 : ℂ)))) (Litex.numberInC (M := M) (81 : ℂ)))) _ _ (Litex.NativeBridge.denotePowNatReal _wd_1_1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ)))) (Litex.NativeBridge.denotePowNatReal _wd_1_1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) ((congrArg₂ (fun (x y : ℂ) => x ^ (2 : ℕ) + y ^ (2 : ℕ)) _litex_x_zero _litex_y_zero).trans (by norm_num))
            · exact Or.inl _litex_left
          ))⟩))) (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)));
          (Litex.abs _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))))) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_2123 (M := M)) (Litex.neg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ))) h_8888 h_8889)
                )
            )
          exact (let _equal_wd_1_0 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)));
        let _wd_1_1 := _wd_1_0;
        (let _litex_call_arg_0 := _wd_1_0;
        let _litex_call_arg_1 := _wd_1_1;
        Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1584 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
          let _atomic_wd_1_0 := _wd_1_1
          exact h_8888) (by
          let _atomic_wd_1_0 := _wd_1_1
          exact h_8888)), (Eq.mpr (congrArg₂ (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (((¬ (_raw_i2 = (M.number (0 : ℂ))))) ∨ ((¬ (_raw_i3 = (M.number (0 : ℂ))))))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) (by
          classical
          have _litex_sum_nonzero : (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := _wd_1_1;
          let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
            let _atomic_wd_2_0 := _wd_3_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          let _wd_2_1 := _wd_2_0;
          (Litex.add _wd_2_0 _wd_2_1 (by
            let _atomic_wd_2_0 := _wd_2_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (81 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_2_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
              let _atomic_wd_3_0 := (_atomic_wd_2_0).val.base
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (9 : ℂ)) ^ (2 : ℕ)) = (81 : ℂ)))) (Litex.numberInC (M := M) (81 : ℂ)))) (by
            let _atomic_wd_2_0 := _wd_2_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (81 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_2_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
              let _atomic_wd_3_0 := (_atomic_wd_2_0).val.base
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (9 : ℂ)) ^ (2 : ℕ)) = (81 : ℂ)))) (Litex.numberInC (M := M) (81 : ℂ))))))
          exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) := (by
          let _atomic_wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := _wd_1_1;
          let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
            let _atomic_wd_2_0 := _wd_3_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          let _wd_2_1 := _wd_2_0;
          (Litex.add _wd_2_0 _wd_2_1 (by
            let _atomic_wd_2_0 := _wd_2_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (81 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_2_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
              let _atomic_wd_3_0 := (_atomic_wd_2_0).val.base
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (9 : ℂ)) ^ (2 : ℕ)) = (81 : ℂ)))) (Litex.numberInC (M := M) (81 : ℂ)))) (by
            let _atomic_wd_2_0 := _wd_2_1
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (81 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_2_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
              let _atomic_wd_3_0 := (_atomic_wd_2_0).val.base
              exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_3_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (9 : ℂ)) ^ (2 : ℕ)) = (81 : ℂ)))) (Litex.numberInC (M := M) (81 : ℂ))))))
          exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (((- (9 : ℂ)) ^ (2 : ℕ)) + ((- (9 : ℂ)) ^ (2 : ℕ))) (0 : ℂ) (Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal ((_atomic_wd_1_0).val.left).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
            let _atomic_wd_2_0 := ((_atomic_wd_1_0).val.left).val.base
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ)))) (Litex.NativeBridge.denotePowNatReal ((_atomic_wd_1_0).val.right).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
            let _atomic_wd_2_0 := ((_atomic_wd_1_0).val.left).val.base
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
          by_cases _litex_left : Litex.Same _wd_1_1 (Litex.number (M := M) (0 : ℂ))
          · apply Or.inr
            intro _litex_right
            have _litex_x_zero : (- (9 : ℂ)) = (0 : ℂ) := Litex.NativeBridge.nativeEqOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (- (9 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (_litex_left)
            have _litex_y_zero : (- (9 : ℂ)) = (0 : ℂ) := Litex.NativeBridge.nativeEqOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (- (9 : ℂ)) (0 : ℂ) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (_litex_right)
            apply _litex_sum_nonzero
            exact Litex.NativeBridge.sameOfDenoteNumber (let _wd_2_0 := (let _wd_3_0 := _wd_1_1;
        let _wd_3_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.powNatReal _wd_3_0 _wd_3_1 (2 : ℕ) (by
          let _atomic_wd_1_0 := _wd_3_0
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_3_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
        let _wd_2_1 := _wd_2_0;
        (Litex.add _wd_2_0 _wd_2_1 (by
          let _atomic_wd_1_0 := _wd_2_1
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (81 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
            let _atomic_wd_2_0 := (_atomic_wd_1_0).val.base
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (9 : ℂ)) ^ (2 : ℕ)) = (81 : ℂ)))) (Litex.numberInC (M := M) (81 : ℂ)))) (by
          let _atomic_wd_1_0 := _wd_2_1
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (81 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
            let _atomic_wd_2_0 := (_atomic_wd_1_0).val.base
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (9 : ℂ)) ^ (2 : ℕ)) = (81 : ℂ)))) (Litex.numberInC (M := M) (81 : ℂ)))))) (Litex.number (M := M) (0 : ℂ)) (((- (9 : ℂ)) ^ (2 : ℕ)) + ((- (9 : ℂ)) ^ (2 : ℕ))) (0 : ℂ) (Litex.NativeBridge.denoteAdd (let _wd_2_0 := _wd_1_1;
        let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
          let _atomic_wd_1_0 := _wd_2_0
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (let _wd_2_0 := _wd_1_1;
        let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
          let _atomic_wd_1_0 := _wd_2_0
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))) (by
          let _atomic_wd_1_0 := (let _wd_2_0 := _wd_1_1;
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_2_0 := _wd_2_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (81 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
            let _atomic_wd_2_0 := (_atomic_wd_1_0).val.base
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (9 : ℂ)) ^ (2 : ℕ)) = (81 : ℂ)))) (Litex.numberInC (M := M) (81 : ℂ)))) (by
          let _atomic_wd_1_0 := (let _wd_2_0 := _wd_1_1;
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_2_0 := _wd_2_0
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))))
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (81 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (_atomic_wd_1_0).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
            let _atomic_wd_2_0 := (_atomic_wd_1_0).val.base
            exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))).trans (congrArg M.number (by norm_num : ((- (9 : ℂ)) ^ (2 : ℕ)) = (81 : ℂ)))) (Litex.numberInC (M := M) (81 : ℂ)))) _ _ (Litex.NativeBridge.denotePowNatReal _wd_1_1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
          let _atomic_wd_1_0 := _wd_1_1
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ)))) (Litex.NativeBridge.denotePowNatReal _wd_1_1 (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
          let _atomic_wd_1_0 := _wd_1_1
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num)))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) ((congrArg₂ (fun (x y : ℂ) => x ^ (2 : ℕ) + y ^ (2 : ℕ)) _litex_x_zero _litex_y_zero).trans (by norm_num))
          · exact Or.inl _litex_left
        ))⟩)));
        let _equal_wd_1_1 := (let _wd_1_0 := (Litex.neg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)));
        (Litex.abs _wd_1_0 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (- (9 : ℂ)) (Litex.R (M := M)) (Litex.NativeBridge.denoteNeg (Litex.number (M := M) (9 : ℂ)) (Litex.numberInC (M := M) (9 : ℂ)) _ (Litex.NativeBridge.denoteNumber (M := M) (9 : ℂ))) (Litex.NativeBridge.numberInROfEq (- (9 : ℂ)) (-9 : ℝ) (by norm_num))))));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((Litex.sameRefl _equal_wd_1_0)).symm.trans ((h_8890).trans (Litex.sameRefl _equal_wd_1_1)))))
        )
      )
  )

noncomputable def _object_i9 := (Litex.formulaFn (M := M) Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) (fun (_raw_i10 : M.Value) => (M.addValue _raw_i10 (M.number (1 : ℂ)))) (by
  intro _raw_i10 h_9104 _
  let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_9104)
  have h_9104 : Litex.In _value_i10 (Litex.Z (M := M)) := h_9104
  change (by
    let _atomic_wd_1_0 := (Litex.add _value_i10 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i10 h_9104) (Litex.numberInC (M := M) (1 : ℂ)))
    exact Litex.In _atomic_wd_1_0 (Litex.Z (M := M)))
  exact (by
    let _atomic_wd_1_0 := (Litex.add _value_i10 (Litex.number (M := M) (1 : ℂ)) (Litex.integerToComplex _value_i10 h_9104) (Litex.numberInC (M := M) (1 : ℂ)))
    exact (Litex.addInZ _value_i10 (Litex.number (M := M) (1 : ℂ)) h_9104 (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))))))
theorem h_9181 : Litex.In (_object_i9 (M := M)) (Litex.fnSet ((_object_i9 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i9 (M := M)))
      )
  )
theorem h_9182 : Litex.Same (_object_i9 (M := M)) (_object_i9 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i9 (M := M)))
      )
  )

noncomputable def _object_w50 := (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) (_object_i9 (M := M)) (Litex.number (M := M) (5 : ℂ)) (h_9181 (M := M)) (Litex.NativeBridge.numberInZOfEq (M := M) (5 : ℂ) (5 : ℤ) (by norm_num)) True.intro)

theorem h_9183 : (by
  let _equal_wd_1_0 := (_object_w50 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w50 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (6 : ℂ)) from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) (M.number (5 : ℂ))) = (M.number (6 : ℂ)) from by
          have _litex_residual : (M.addValue (M.number (5 : ℂ)) (M.number (1 : ℂ))) = (M.number (6 : ℂ)) := (let _equal_wd_2_0 := (Litex.add (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInC (M := M) (5 : ℂ)) (Litex.numberInC (M := M) (1 : ℂ)));
          (show Litex.Same _equal_wd_2_0 (Litex.number (M := M) (6 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_2_0 (Litex.number (M := M) (6 : ℂ)) ((5 : ℂ) + (1 : ℂ)) (6 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.number (M := M) (5 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteNumber (M := M) (5 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (1 : ℂ))) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (by norm_num))))
          exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) (M.number (5 : ℂ))))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) (M.number (5 : ℂ))) = (M.addValue (M.number (5 : ℂ)) (M.number (1 : ℂ))) from by
          let _litex_original := _equal_wd_1_0
          let _litex_literal := (let _wd_1_0 := (_object_i9 (M := M));
          let _wd_1_1 := (Litex.number (M := M) (5 : ℂ));
          (Litex.call Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) _wd_1_0 _wd_1_1 (Litex.formulaFnInFnSet _wd_1_0) (Litex.NativeBridge.numberInZOfEq (M := M) (5 : ℂ) (5 : ℤ) (by norm_num)) True.intro))
          have _litex_call_eq := Litex.callCongr _litex_original _litex_literal (h_9182 (M := M)) (Litex.sameRefl _litex_original.val.argument)
          have _litex_beta := Litex.callFormula_denote Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) (fun (_raw_i10 : M.Value) => (M.addValue _raw_i10 (M.number (1 : ℂ)))) (by intro _x _hx _hg; exact _litex_literal.val.function.wd _x ((Litex.FunctionSignature.one_domain Litex.StandardSetValue.integer Litex.StandardSetValue.integer (fun (_raw_i10 : M.Value) => True) _x).mpr ⟨_hx, _hg⟩)) _litex_literal.val.argument _litex_literal.wd.2.1 _litex_literal.wd.2.2
          exact _litex_call_eq.trans (_litex_beta.trans (show (fun (_raw_i10 : M.Value) => (M.addValue _raw_i10 (M.number (1 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (M.number (5 : ℂ)) (M.number (1 : ℂ))) from rfl))
        ))).trans _litex_residual)))
      )
  )

noncomputable def _object_w53 := (let _wd_1_0 := (_object_w50 (M := M));
let _wd_1_1 := (Litex.number (M := M) (15 : ℂ));
(Litex.gcd _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := (_object_w50 (M := M))
  exact (by
    let _litex_return_call := (_object_w50 (M := M))
    exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.Z (M := M)) (Litex.Z (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.Z (M := M))) (Litex.callInOutput _litex_return_call))) (Litex.NativeBridge.numberInZOfEq (M := M) (15 : ℂ) (15 : ℤ) (by norm_num)) (by
  classical
  apply Classical.byContradiction
  intro _negative_disjunction
  have h_10715 : Litex.Same _wd_1_1 (Litex.number (M := M) (0 : ℂ)) :=
    (by
      litex_checked_step =>
        exact (
          (Classical.byContradiction (fun _branch => _negative_disjunction (Or.inr _branch)))
        )
    )
  exact _negative_disjunction (Or.inl (by
    let _atomic_wd_1_0 := (_object_w50 (M := M))
    exact (Litex.notSameOfSame (Litex.number (M := M) (6 : ℂ)) _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (Litex.number (M := M) (0 : ℂ)) ((h_9183 (M := M))).symm (Litex.sameRefl (Litex.number (M := M) (0 : ℂ))) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (6 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))))
)))

noncomputable def _object_w54 := (Litex.gcd (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (15 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (6 : ℂ) (6 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (15 : ℂ) (15 : ℤ) (by norm_num)) (by
  classical
  have _litex_sum_nonzero : (by
  let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.powNatReal (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
  let _wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (15 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (15 : ℂ) (15 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_2_0 := _wd_1_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (36 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)))).trans (congrArg M.number (by norm_num : ((6 : ℂ) ^ (2 : ℕ)) = (36 : ℂ)))) (Litex.numberInC (M := M) (36 : ℂ)))) (by
    let _atomic_wd_2_0 := _wd_1_1
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (225 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (15 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (15 : ℂ) (15 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (15 : ℂ)))).trans (congrArg M.number (by norm_num : ((15 : ℂ) ^ (2 : ℕ)) = (225 : ℂ)))) (Litex.numberInC (M := M) (225 : ℂ))))))
  exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ))) := (by
  let _atomic_wd_1_0 := (let _wd_1_0 := (Litex.powNatReal (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
  let _wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (15 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (15 : ℂ) (15 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
  (Litex.add _wd_1_0 _wd_1_1 (by
    let _atomic_wd_2_0 := _wd_1_0
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (36 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)))).trans (congrArg M.number (by norm_num : ((6 : ℂ) ^ (2 : ℕ)) = (36 : ℂ)))) (Litex.numberInC (M := M) (36 : ℂ)))) (by
    let _atomic_wd_2_0 := _wd_1_1
    exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_2_0 (225 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (15 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (15 : ℂ) (15 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (15 : ℂ)))).trans (congrArg M.number (by norm_num : ((15 : ℂ) ^ (2 : ℕ)) = (225 : ℂ)))) (Litex.numberInC (M := M) (225 : ℂ))))))
  exact (Litex.NativeBridge.notSameOfDenoteNumber _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)) (((6 : ℂ) ^ (2 : ℕ)) + ((15 : ℂ) ^ (2 : ℕ))) (0 : ℂ) (Litex.NativeBridge.denoteAdd (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (_atomic_wd_1_0).wd.1 (_atomic_wd_1_0).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (15 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (15 : ℂ) (15 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (15 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num)))
  by_cases _litex_left : Litex.Same (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (0 : ℂ))
  · apply Or.inr
    intro _litex_right
    have _litex_x_zero : (6 : ℂ) = (0 : ℂ) := Litex.NativeBridge.nativeEqOfDenoteNumber (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (6 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (_litex_left)
    have _litex_y_zero : (15 : ℂ) = (0 : ℂ) := Litex.NativeBridge.nativeEqOfDenoteNumber (Litex.number (M := M) (15 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (15 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (15 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (_litex_right)
    apply _litex_sum_nonzero
    exact Litex.NativeBridge.sameOfDenoteNumber (let _wd_1_0 := (Litex.powNatReal (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
let _wd_1_1 := (Litex.powNatReal (Litex.number (M := M) (15 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (15 : ℂ) (15 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)));
(Litex.add _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := _wd_1_0
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (36 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)))).trans (congrArg M.number (by norm_num : ((6 : ℂ) ^ (2 : ℕ)) = (36 : ℂ)))) (Litex.numberInC (M := M) (36 : ℂ)))) (by
  let _atomic_wd_1_0 := _wd_1_1
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (225 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (15 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (15 : ℂ) (15 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (15 : ℂ)))).trans (congrArg M.number (by norm_num : ((15 : ℂ) ^ (2 : ℕ)) = (225 : ℂ)))) (Litex.numberInC (M := M) (225 : ℂ)))))) (Litex.number (M := M) (0 : ℂ)) (((6 : ℂ) ^ (2 : ℕ)) + ((15 : ℂ) ^ (2 : ℕ))) (0 : ℂ) (Litex.NativeBridge.denoteAdd (Litex.powNatReal (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (Litex.powNatReal (Litex.number (M := M) (15 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (15 : ℂ) (15 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))) (by
  let _atomic_wd_1_0 := (Litex.powNatReal (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (36 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ)))).trans (congrArg M.number (by norm_num : ((6 : ℂ) ^ (2 : ℕ)) = (36 : ℂ)))) (Litex.numberInC (M := M) (36 : ℂ)))) (by
  let _atomic_wd_1_0 := (Litex.powNatReal (Litex.number (M := M) (15 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (15 : ℂ) (15 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)))
  exact (Litex.NativeBridge.inOfDenoteNumber _atomic_wd_1_0 (225 : ℂ) (Litex.C (M := M)) (((Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (15 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (15 : ℂ) (15 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (15 : ℂ)))).trans (congrArg M.number (by norm_num : ((15 : ℂ) ^ (2 : ℕ)) = (225 : ℂ)))) (Litex.numberInC (M := M) (225 : ℂ)))) _ _ (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (6 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (6 : ℂ) (6 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))) (Litex.NativeBridge.denotePowNatReal (Litex.number (M := M) (15 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (Litex.NativeBridge.numberInROfEq (M := M) (15 : ℂ) (15 : ℝ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteNumber (M := M) (15 : ℂ)))) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) ((congrArg₂ (fun (x y : ℂ) => x ^ (2 : ℕ) + y ^ (2 : ℕ)) _litex_x_zero _litex_y_zero).trans (by norm_num))
  · exact Or.inl _litex_left
))

theorem h_9281 : (by
  let _equal_wd_1_0 := (_object_w53 (M := M))
  let _equal_wd_1_1 := (_object_w54 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (congrArg₂ (Litex.gcdLcmValue (M := M) false) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i9 (M := M))) (M.number (5 : ℂ))) = (M.number (6 : ℂ)) from (h_9183 (M := M))) (show (M.number (15 : ℂ)) = (M.number (15 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)))
      )
  )

theorem h_10848 : (by
  let _equal_wd_1_0 := (_object_w54 (M := M))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (_object_w54 (M := M));
        (show Litex.Same _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) from (Litex.NativeBridge.sameOfDenoteNumber _equal_wd_1_0 (Litex.number (M := M) (3 : ℂ)) (3 : ℂ) (3 : ℂ) (let _intop := (_object_w54 (M := M));
        let _member : Litex.In _intop Litex.C := Litex.naturalToComplex _intop (Litex.gcdInN _intop);
        (Litex.gcdDenoteInt _intop (6 : ℤ) (15 : ℤ) (((Litex.NativeBridge.denoteNumber (M := M) (6 : ℂ))).trans (congrArg M.number (by norm_num : (6 : ℂ) = ((6 : ℤ) : ℂ)))) (((Litex.NativeBridge.denoteNumber (M := M) (15 : ℂ))).trans (congrArg M.number (by norm_num : (15 : ℂ) = ((15 : ℤ) : ℂ))))).trans (congrArg M.number (by norm_num [Int.gcd_eq_natAbs_gcd_natAbs]))) (Litex.NativeBridge.denoteNumber (M := M) (3 : ℂ)) (by norm_num))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_gcd_x5f_lcm_x5f_functions_x2f_statement_x2e_lit
