import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_line_x5f_membership_x5f_condition_x2f_statement_x2e_lit

universe u v85 v86 v87
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

noncomputable def _object_i1 := (Litex.formulaFnOn (Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))]) (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
  have _finiteProof_1 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) _raw_i3 (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i2 (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) _raw_i3 (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i2 (M.number (2 : ℂ))))])) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
  have _litex_checked_return : ∀ (_raw_i2 : M.Value) (_raw_i3 : M.Value), M.mem _raw_i2 (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) → M.mem _raw_i3 (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) → ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) _raw_i2 _raw_i3) → M.mem ((fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) _raw_i3 (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i2 (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) _raw_i3 (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i2 (M.number (2 : ℂ))))])) _raw_i2 _raw_i3) (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) := (by
    intro _raw_i2 _raw_i3 h_17 h_20 _
    let _value_i2 := Litex.semanticObject (M := M) _raw_i2 (M.member_isSet h_17)
    have h_17 : Litex.In _value_i2 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) := h_17
    let _object_h18 := (Litex.cartCall _value_i2 _ (Litex.number (M := M) (1 : ℂ)) h_17 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_18 : Litex.In _object_h18 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_17 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h19 := (Litex.cartCall _value_i2 _ (Litex.number (M := M) (2 : ℂ)) h_17 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_19 : Litex.In _object_h19 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_17 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    let _value_i3 := Litex.semanticObject (M := M) _raw_i3 (M.member_isSet h_20)
    have h_20 : Litex.In _value_i3 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) := h_20
    let _object_h21 := (Litex.cartCall _value_i3 _ (Litex.number (M := M) (1 : ℂ)) h_20 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_21 : Litex.In _object_h21 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_20 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h22 := (Litex.cartCall _value_i3 _ (Litex.number (M := M) (2 : ℂ)) h_20 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_22 : Litex.In _object_h22 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_20 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    change (by
      let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := _object_h21;
      let _wd_2_1 := _object_h18;
      (Litex.sub _wd_2_0 _wd_2_1 (by
        let _atomic_wd_2_0 := _object_h21
        exact (M.real_subset_complex _ h_21)) (by
        let _atomic_wd_2_0 := _object_h18
        exact (M.real_subset_complex _ h_18))));
      let _wd_1_1 := (let _wd_2_0 := _object_h22;
      let _wd_2_1 := _object_h19;
      (Litex.sub _wd_2_0 _wd_2_1 (by
        let _atomic_wd_2_0 := _object_h22
        exact (M.real_subset_complex _ h_22)) (by
        let _atomic_wd_2_0 := _object_h19
        exact (M.real_subset_complex _ h_19))));
      (let _productChild_0 := _wd_1_0;
      let _productChild_1 := _wd_1_1;
      Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
        have _finiteProof_0 := ((Litex.isSet _productChild_0))
        have _finiteProof_1 := ((Litex.isSet _productChild_1))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )))
      let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
      exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
    exact (by
      let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := _object_h21;
      let _wd_2_1 := _object_h18;
      (Litex.sub _wd_2_0 _wd_2_1 (by
        let _atomic_wd_2_0 := _object_h21
        exact (M.real_subset_complex _ h_21)) (by
        let _atomic_wd_2_0 := _object_h18
        exact (M.real_subset_complex _ h_18))));
      let _wd_1_1 := (let _wd_2_0 := _object_h22;
      let _wd_2_1 := _object_h19;
      (Litex.sub _wd_2_0 _wd_2_1 (by
        let _atomic_wd_2_0 := _object_h22
        exact (M.real_subset_complex _ h_22)) (by
        let _atomic_wd_2_0 := _object_h19
        exact (M.real_subset_complex _ h_19))));
      (let _productChild_0 := _wd_1_0;
      let _productChild_1 := _wd_1_1;
      Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
        have _finiteProof_0 := ((Litex.isSet _productChild_0))
        have _finiteProof_1 := ((Litex.isSet _productChild_1))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )))
      let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
      exact (by
        let _checked_domain_target := (by
        have _checked_header : ∀ (_raw_i22 : M.Value), M.mem _raw_i22 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) → ((fun (_raw_i22 : M.Value) => True) _raw_i22) → True := by
          intro _raw_i22 h_1346 _
          let _value_i22 := Litex.semanticObject (M := M) _raw_i22 (M.member_isSet h_1346)
          have h_1346 : Litex.In _value_i22 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) := h_1346
          exact True.intro
        exact Litex.fnSet (Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.denote (Litex.union (Litex.R (M := M)) (Litex.R (M := M)))) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.isSet (Litex.union (Litex.R (M := M)) (Litex.R (M := M)))) (fun (_litex_input : M.Value) => (fun (_raw_i22 : M.Value) => True) _litex_input)))
        let _function := (let _wd_1_0 := (let _wd_2_0 := _object_h21;
      let _wd_2_1 := _object_h18;
      (Litex.sub _wd_2_0 _wd_2_1 (by
        let _atomic_wd_2_0 := _object_h21
        exact (M.real_subset_complex _ h_21)) (by
        let _atomic_wd_2_0 := _object_h18
        exact (M.real_subset_complex _ h_18))));
      let _wd_1_1 := (let _wd_2_0 := _object_h22;
      let _wd_2_1 := _object_h19;
      (Litex.sub _wd_2_0 _wd_2_1 (by
        let _atomic_wd_2_0 := _object_h22
        exact (M.real_subset_complex _ h_22)) (by
        let _atomic_wd_2_0 := _object_h19
        exact (M.real_subset_complex _ h_19))));
      (let _productChild_0 := _wd_1_0;
      let _productChild_1 := _wd_1_1;
      Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
        have _finiteProof_0 := ((Litex.isSet _productChild_0))
        have _finiteProof_1 := ((Litex.isSet _productChild_1))
        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
      )))
        let _tuple := _atomic_wd_1_0
        let _cart := _atomic_wd_1_1
        let _target := _atomic_wd_1_1
        have _tupleMember : Litex.In _tuple _cart := Litex.tupleInCart _tuple _cart (by
          have _finiteProof_0 := ((by
            let _atomic_wd_2_0 := (let _wd_1_0 := _object_h21;
            let _wd_1_1 := _object_h18;
            (Litex.sub _wd_1_0 _wd_1_1 (by
              let _atomic_wd_3_0 := _object_h21
              exact (M.real_subset_complex _ h_21)) (by
              let _atomic_wd_3_0 := _object_h18
              exact (M.real_subset_complex _ h_18))))
            exact (Litex.subInR (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right h_21 h_18)))
          have _finiteProof_1 := ((by
            let _atomic_wd_2_0 := (let _wd_1_0 := _object_h22;
            let _wd_1_1 := _object_h19;
            (Litex.sub _wd_1_0 _wd_1_1 (by
              let _atomic_wd_3_0 := _object_h22
              exact (M.real_subset_complex _ h_22)) (by
              let _atomic_wd_3_0 := _object_h19
              exact (M.real_subset_complex _ h_19))))
            exact (Litex.subInR (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right h_22 h_19)))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )
        have _tupleSame : Litex.Same _function _tuple := (show @Eq M.Value _ _ from Eq.refl _)
        have _carrierSame : Litex.Same _target _cart := (show @Eq M.Value _ _ from Eq.refl _)
        exact Litex.inOfSame _tuple _function _cart _target _tupleSame.symm _carrierSame.symm _tupleMember)))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))]) (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
  have _finiteProof_1 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
  exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard))
theorem h_1859 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (Litex.formulaFnInFnSet (_object_i1 (M := M)))
theorem h_1860 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (Litex.sameRefl (_object_i1 (M := M)))

noncomputable def _object_i40 := (Litex.formulaFnOn (Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
  have _finiteProof_1 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i41 : M.Value) (_raw_i42 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i41 : M.Value) (_raw_i42 : M.Value) => (M.subValue (M.mulValue (Litex.FunctionSemantics.callValue (M := M) _raw_i41 (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i42 (M.number (2 : ℂ)))) (M.mulValue (Litex.FunctionSemantics.callValue (M := M) _raw_i41 (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i42 (M.number (1 : ℂ)))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
  have _litex_checked_return : ∀ (_raw_i41 : M.Value) (_raw_i42 : M.Value), M.mem _raw_i41 (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) → M.mem _raw_i42 (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) → ((fun (_raw_i41 : M.Value) (_raw_i42 : M.Value) => True) _raw_i41 _raw_i42) → M.mem ((fun (_raw_i41 : M.Value) (_raw_i42 : M.Value) => (M.subValue (M.mulValue (Litex.FunctionSemantics.callValue (M := M) _raw_i41 (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i42 (M.number (2 : ℂ)))) (M.mulValue (Litex.FunctionSemantics.callValue (M := M) _raw_i41 (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i42 (M.number (1 : ℂ)))))) _raw_i41 _raw_i42) (Litex.denote (Litex.R (M := M))) := (by
    intro _raw_i41 _raw_i42 h_1877 h_1880 _
    let _value_i41 := Litex.semanticObject (M := M) _raw_i41 (M.member_isSet h_1877)
    have h_1877 : Litex.In _value_i41 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) := h_1877
    let _object_h1878 := (Litex.cartCall _value_i41 _ (Litex.number (M := M) (1 : ℂ)) h_1877 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_1878 : Litex.In _object_h1878 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_1877 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h1879 := (Litex.cartCall _value_i41 _ (Litex.number (M := M) (2 : ℂ)) h_1877 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_1879 : Litex.In _object_h1879 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_1877 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    let _value_i42 := Litex.semanticObject (M := M) _raw_i42 (M.member_isSet h_1880)
    have h_1880 : Litex.In _value_i42 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) := h_1880
    let _object_h1881 := (Litex.cartCall _value_i42 _ (Litex.number (M := M) (1 : ℂ)) h_1880 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_1881 : Litex.In _object_h1881 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_1880 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h1882 := (Litex.cartCall _value_i42 _ (Litex.number (M := M) (2 : ℂ)) h_1880 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_1882 : Litex.In _object_h1882 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_1880 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    change (by
      let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := _object_h1878;
      let _wd_2_1 := _object_h1882;
      (Litex.mul _wd_2_0 _wd_2_1 (by
        let _atomic_wd_2_0 := _object_h1878
        exact (M.real_subset_complex _ h_1878)) (by
        let _atomic_wd_2_0 := _object_h1882
        exact (M.real_subset_complex _ h_1882))));
      let _wd_1_1 := (let _wd_2_0 := _object_h1879;
      let _wd_2_1 := _object_h1881;
      (Litex.mul _wd_2_0 _wd_2_1 (by
        let _atomic_wd_2_0 := _object_h1879
        exact (M.real_subset_complex _ h_1879)) (by
        let _atomic_wd_2_0 := _object_h1881
        exact (M.real_subset_complex _ h_1881))));
      (Litex.sub _wd_1_0 _wd_1_1 (by
        let _atomic_wd_2_0 := (let _wd_2_0 := _object_h1878;
        let _wd_2_1 := _object_h1882;
        (Litex.mul _wd_2_0 _wd_2_1 (by
          let _atomic_wd_3_0 := _object_h1878
          exact (M.real_subset_complex _ h_1878)) (by
          let _atomic_wd_3_0 := _object_h1882
          exact (M.real_subset_complex _ h_1882))))
        exact (Litex.mulInC (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (M.real_subset_complex _ h_1878) (M.real_subset_complex _ h_1882))) (by
        let _atomic_wd_2_0 := (let _wd_2_0 := _object_h1879;
        let _wd_2_1 := _object_h1881;
        (Litex.mul _wd_2_0 _wd_2_1 (by
          let _atomic_wd_3_0 := _object_h1879
          exact (M.real_subset_complex _ h_1879)) (by
          let _atomic_wd_3_0 := _object_h1881
          exact (M.real_subset_complex _ h_1881))))
        exact (Litex.mulInC (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (M.real_subset_complex _ h_1879) (M.real_subset_complex _ h_1881)))))
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := _object_h1878;
      let _wd_2_1 := _object_h1882;
      (Litex.mul _wd_2_0 _wd_2_1 (by
        let _atomic_wd_2_0 := _object_h1878
        exact (M.real_subset_complex _ h_1878)) (by
        let _atomic_wd_2_0 := _object_h1882
        exact (M.real_subset_complex _ h_1882))));
      let _wd_1_1 := (let _wd_2_0 := _object_h1879;
      let _wd_2_1 := _object_h1881;
      (Litex.mul _wd_2_0 _wd_2_1 (by
        let _atomic_wd_2_0 := _object_h1879
        exact (M.real_subset_complex _ h_1879)) (by
        let _atomic_wd_2_0 := _object_h1881
        exact (M.real_subset_complex _ h_1881))));
      (Litex.sub _wd_1_0 _wd_1_1 (by
        let _atomic_wd_2_0 := (let _wd_2_0 := _object_h1878;
        let _wd_2_1 := _object_h1882;
        (Litex.mul _wd_2_0 _wd_2_1 (by
          let _atomic_wd_3_0 := _object_h1878
          exact (M.real_subset_complex _ h_1878)) (by
          let _atomic_wd_3_0 := _object_h1882
          exact (M.real_subset_complex _ h_1882))))
        exact (Litex.mulInC (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (M.real_subset_complex _ h_1878) (M.real_subset_complex _ h_1882))) (by
        let _atomic_wd_2_0 := (let _wd_2_0 := _object_h1879;
        let _wd_2_1 := _object_h1881;
        (Litex.mul _wd_2_0 _wd_2_1 (by
          let _atomic_wd_3_0 := _object_h1879
          exact (M.real_subset_complex _ h_1879)) (by
          let _atomic_wd_3_0 := _object_h1881
          exact (M.real_subset_complex _ h_1881))))
        exact (Litex.mulInC (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (M.real_subset_complex _ h_1879) (M.real_subset_complex _ h_1881)))))
      exact (Litex.subInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.mulInR ((_atomic_wd_1_0).val.left).val.left ((_atomic_wd_1_0).val.left).val.right h_1878 h_1882) (Litex.mulInR ((_atomic_wd_1_0).val.right).val.left ((_atomic_wd_1_0).val.right).val.right h_1879 h_1881))))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
  have _finiteProof_1 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i41 : M.Value) (_raw_i42 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
  exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard))
theorem h_4141 : Litex.In (_object_i40 (M := M)) (Litex.fnSet ((_object_i40 (M := M))).val.signature) :=
  (Litex.formulaFnInFnSet (_object_i40 (M := M)))
theorem h_4142 : Litex.Same (_object_i40 (M := M)) (_object_i40 (M := M)) :=
  (Litex.sameRefl (_object_i40 (M := M)))

noncomputable def _object_i77 := (Litex.formulaFnOn (Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))]) (Litex.denote (let _wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))));
(Litex.powerSet _wd_1_0))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
  have _finiteProof_1 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet (let _wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))));
(Litex.powerSet _wd_1_0))) (fun (_litex_input : M.Value) => (fun (_raw_i78 : M.Value) (_raw_i79 : M.Value) => (¬ (_raw_i78 = _raw_i79))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i78 : M.Value) (_raw_i79 : M.Value) => (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_raw_i80 : M.Value) => ∃ (_ : M.mem _raw_i80 (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)])), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i40 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i78, _raw_i80])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i78, _raw_i79]))])) = (M.number (0 : ℂ)))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
  have _litex_checked_return : ∀ (_raw_i78 : M.Value) (_raw_i79 : M.Value), M.mem _raw_i78 (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) → M.mem _raw_i79 (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) → ((fun (_raw_i78 : M.Value) (_raw_i79 : M.Value) => (¬ (_raw_i78 = _raw_i79))) _raw_i78 _raw_i79) → M.mem ((fun (_raw_i78 : M.Value) (_raw_i79 : M.Value) => (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_raw_i80 : M.Value) => ∃ (_ : M.mem _raw_i80 (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)])), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i40 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i78, _raw_i80])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i78, _raw_i79]))])) = (M.number (0 : ℂ)))))) _raw_i78 _raw_i79) (Litex.denote (let _wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))));
(Litex.powerSet _wd_1_0))) := (by
    intro _raw_i78 _raw_i79 h_4191 h_4194 h_4143
    let _value_i78 := Litex.semanticObject (M := M) _raw_i78 (M.member_isSet h_4191)
    have h_4191 : Litex.In _value_i78 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) := h_4191
    let _object_h4192 := (Litex.cartCall _value_i78 _ (Litex.number (M := M) (1 : ℂ)) h_4191 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_4192 : Litex.In _object_h4192 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_4191 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h4193 := (Litex.cartCall _value_i78 _ (Litex.number (M := M) (2 : ℂ)) h_4191 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_4193 : Litex.In _object_h4193 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_4191 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    let _value_i79 := Litex.semanticObject (M := M) _raw_i79 (M.member_isSet h_4194)
    have h_4194 : Litex.In _value_i79 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) := h_4194
    let _object_h4195 := (Litex.cartCall _value_i79 _ (Litex.number (M := M) (1 : ℂ)) h_4194 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_4195 : Litex.In _object_h4195 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_4194 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h4196 := (Litex.cartCall _value_i79 _ (Litex.number (M := M) (2 : ℂ)) h_4194 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_4196 : Litex.In _object_h4196 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_4194 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    have h_4143 : ¬ Litex.Same _value_i78 _value_i79 :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i78 = _raw_i79))
              exact h_4143)
          )
      )
    change (by
      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) (fun (_value_i80 : Litex.Obj (M := M) M.Value) (h_4341 : Litex.In _value_i80 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) => Litex.Same (let _object_w16 := (let _litex_call_arg_0 := _value_i78;
      let _litex_call_arg_1 := _value_i80;
      Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1859 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact h_4191) (by
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact h_4341)), True.intro⟩));
      let _object_w17 := (let _litex_call_arg_0 := _value_i78;
      let _litex_call_arg_1 := _value_i79;
      Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1859 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact h_4191) (by
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact h_4194)), True.intro⟩));
      (let _litex_call_arg_0 := _object_w16;
      let _litex_call_arg_1 := _object_w17;
      Litex.callOn ((_object_i40 (M := M))).val.signature (_object_i40 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_4141 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
        let _atomic_wd_2_0 := _object_w16
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact (by
          let _litex_return_call := _object_w16
          exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_2_1 _atomic_wd_2_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_2_1) (Litex.callOnInOutput _litex_return_call))) (by
        let _atomic_wd_2_0 := _object_w17
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact (by
          let _litex_return_call := _object_w17
          exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_2_1 _atomic_wd_2_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_2_1) (Litex.callOnInOutput _litex_return_call)))), True.intro⟩))) (Litex.number (M := M) (0 : ℂ))))
      let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))));
      (Litex.powerSet _wd_1_0))
      exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
    exact (by
      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) (fun (_value_i80 : Litex.Obj (M := M) M.Value) (h_4341 : Litex.In _value_i80 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) => Litex.Same (let _object_w16 := (let _litex_call_arg_0 := _value_i78;
      let _litex_call_arg_1 := _value_i80;
      Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1859 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact h_4191) (by
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact h_4341)), True.intro⟩));
      let _object_w17 := (let _litex_call_arg_0 := _value_i78;
      let _litex_call_arg_1 := _value_i79;
      Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1859 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact h_4191) (by
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact h_4194)), True.intro⟩));
      (let _litex_call_arg_0 := _object_w16;
      let _litex_call_arg_1 := _object_w17;
      Litex.callOn ((_object_i40 (M := M))).val.signature (_object_i40 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_4141 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
        let _atomic_wd_2_0 := _object_w16
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact (by
          let _litex_return_call := _object_w16
          exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_2_1 _atomic_wd_2_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_2_1) (Litex.callOnInOutput _litex_return_call))) (by
        let _atomic_wd_2_0 := _object_w17
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact (by
          let _litex_return_call := _object_w17
          exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_2_1 _atomic_wd_2_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_2_1) (Litex.callOnInOutput _litex_return_call)))), True.intro⟩))) (Litex.number (M := M) (0 : ℂ))))
      let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))));
      (Litex.powerSet _wd_1_0))
      exact ((Litex.inPowerSet_iff _atomic_wd_1_0 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))).mpr (by
        let _atomic_wd_2_0 := (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) (fun (_value_i80 : Litex.Obj (M := M) M.Value) (h_4661 : Litex.In _value_i80 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) => Litex.Same (let _object_w24 := (let _litex_call_arg_0 := _value_i78;
        let _litex_call_arg_1 := _value_i80;
        Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1859 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
          let _atomic_wd_3_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
          exact h_4191) (by
          let _atomic_wd_3_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
          exact h_4661)), True.intro⟩));
        let _object_w25 := (let _litex_call_arg_0 := _value_i78;
        let _litex_call_arg_1 := _value_i79;
        Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1859 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
          let _atomic_wd_3_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
          exact h_4191) (by
          let _atomic_wd_3_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
          exact h_4194)), True.intro⟩));
        (let _litex_call_arg_0 := _object_w24;
        let _litex_call_arg_1 := _object_w25;
        Litex.callOn ((_object_i40 (M := M))).val.signature (_object_i40 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_4141 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
          let _atomic_wd_3_0 := _object_w24
          let _atomic_wd_3_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
          exact (by
            let _litex_return_call := _object_w24
            exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_3_1 _atomic_wd_3_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_3_1) (Litex.callOnInOutput _litex_return_call))) (by
          let _atomic_wd_3_0 := _object_w25
          let _atomic_wd_3_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
          exact (by
            let _litex_return_call := _object_w25
            exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_3_1 _atomic_wd_3_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_3_1) (Litex.callOnInOutput _litex_return_call)))), True.intro⟩))) (Litex.number (M := M) (0 : ℂ))))
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact (by
          let _set := _atomic_wd_2_0
          exact Litex.setBuilderSubset _set.val.bound _set.val.predicate)))))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))]) (Litex.denote (let _wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))));
(Litex.powerSet _wd_1_0))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
  have _finiteProof_1 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet (let _wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))));
(Litex.powerSet _wd_1_0))) (fun (_litex_input : M.Value) => (fun (_raw_i78 : M.Value) (_raw_i79 : M.Value) => (¬ (_raw_i78 = _raw_i79))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
  exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard))
theorem h_4810 : Litex.In (_object_i77 (M := M)) (Litex.fnSet ((_object_i77 (M := M))).val.signature) :=
  (Litex.formulaFnInFnSet (_object_i77 (M := M)))
theorem h_4811 : Litex.Same (_object_i77 (M := M)) (_object_i77 (M := M)) :=
  (Litex.sameRefl (_object_i77 (M := M)))

theorem h_4815 : ∀ {_Host_i85 : Type v85} [_rep_i85 : Litex.Representation M _Host_i85] (_value_i85 : Litex.Obj (M := M) _Host_i85) (h_4819 : Litex.In _value_i85 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) {_Host_i86 : Type v86} [_rep_i86 : Litex.Representation M _Host_i86] (_value_i86 : Litex.Obj (M := M) _Host_i86) (h_4822 : Litex.In _value_i86 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) {_Host_i87 : Type v87} [_rep_i87 : Litex.Representation M _Host_i87] (_value_i87 : Litex.Obj (M := M) _Host_i87) (h_4825 : Litex.In _value_i87 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) (h_4812 : ¬ Litex.Same _value_i85 _value_i86) (h_4813 : (by
  let _atomic_wd_1_1 := (let _litex_call_arg_0 := _value_i85;
  let _litex_call_arg_1 := _value_i86;
  Litex.callOn ((_object_i77 (M := M))).val.signature (_object_i77 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_4810 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
    exact h_4819) (by
    let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
    exact h_4822)), (Eq.mpr (congrArg₂ (fun (_raw_i78 : M.Value) (_raw_i79 : M.Value) => (¬ (_raw_i78 = _raw_i79))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) h_4812)⟩))
  exact Litex.In _value_i87 _atomic_wd_1_1)), (by
  let _equal_wd_1_0 := (let _object_w33 := (let _litex_call_arg_0 := _value_i85;
  let _litex_call_arg_1 := _value_i87;
  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1859 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
    exact h_4819) (by
    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
    exact h_4825)), True.intro⟩));
  let _object_w34 := (let _litex_call_arg_0 := _value_i85;
  let _litex_call_arg_1 := _value_i86;
  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1859 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
    exact h_4819) (by
    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
    exact h_4822)), True.intro⟩));
  (let _litex_call_arg_0 := _object_w33;
  let _litex_call_arg_1 := _object_w34;
  Litex.callOn ((_object_i40 (M := M))).val.signature (_object_i40 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_4141 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_0 := _object_w33
    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
    exact (by
      let _litex_return_call := _object_w33
      exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_1_1 _atomic_wd_1_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_1_1) (Litex.callOnInOutput _litex_return_call))) (by
    let _atomic_wd_1_0 := _object_w34
    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
    exact (by
      let _litex_return_call := _object_w34
      exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_1_1 _atomic_wd_1_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_1_1) (Litex.callOnInOutput _litex_return_call)))), True.intro⟩)))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    intro _Host_i85 _rep_i85 _value_i85 h_4819 _Host_i86 _rep_i86 _value_i86 h_4822 _Host_i87 _rep_i87 _value_i87 h_4825 h_4812 h_4813
    let _object_h4820 := (Litex.cartCall _value_i85 _ (Litex.number (M := M) (1 : ℂ)) h_4819 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_4820 : Litex.In _object_h4820 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_4819 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h4821 := (Litex.cartCall _value_i85 _ (Litex.number (M := M) (2 : ℂ)) h_4819 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_4821 : Litex.In _object_h4821 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_4819 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    let _object_h4823 := (Litex.cartCall _value_i86 _ (Litex.number (M := M) (1 : ℂ)) h_4822 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_4823 : Litex.In _object_h4823 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_4822 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h4824 := (Litex.cartCall _value_i86 _ (Litex.number (M := M) (2 : ℂ)) h_4822 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_4824 : Litex.In _object_h4824 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_4822 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    let _object_h4826 := (Litex.cartCall _value_i87 _ (Litex.number (M := M) (1 : ℂ)) h_4825 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_4826 : Litex.In _object_h4826 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_4825 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h4827 := (Litex.cartCall _value_i87 _ (Litex.number (M := M) (2 : ℂ)) h_4825 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_4827 : Litex.In _object_h4827 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_4825 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    have h_5012 : Litex.In _value_i85 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) :=
      (by
        litex_checked_step =>
          exact (
            h_4819
          )
      )
    have h_5015 : Litex.In _value_i86 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) :=
      (by
        litex_checked_step =>
          exact (
            h_4822
          )
      )
    have h_5018 : Litex.In _value_i87 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) :=
      (by
        litex_checked_step =>
          exact (
            h_4825
          )
      )
    let _object_h5013 := (Litex.cartCall _value_i85 _ (Litex.number (M := M) (1 : ℂ)) h_5012 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_5013 : Litex.In _object_h5013 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_5012 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h5014 := (Litex.cartCall _value_i85 _ (Litex.number (M := M) (2 : ℂ)) h_5012 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_5014 : Litex.In _object_h5014 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_5012 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    let _object_h5016 := (Litex.cartCall _value_i86 _ (Litex.number (M := M) (1 : ℂ)) h_5015 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_5016 : Litex.In _object_h5016 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_5015 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h5017 := (Litex.cartCall _value_i86 _ (Litex.number (M := M) (2 : ℂ)) h_5015 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_5017 : Litex.In _object_h5017 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_5015 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    let _object_h5019 := (Litex.cartCall _value_i87 _ (Litex.number (M := M) (1 : ℂ)) h_5018 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_5019 : Litex.In _object_h5019 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_5018 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h5020 := (Litex.cartCall _value_i87 _ (Litex.number (M := M) (2 : ℂ)) h_5018 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_5020 : Litex.In _object_h5020 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_5018 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    let _object_w49 := (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) (fun (_value_i88 : Litex.Obj (M := M) M.Value) (h_5055 : Litex.In _value_i88 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) => Litex.Same (let _object_w37 := (let _litex_call_arg_0 := _value_i85;
    let _litex_call_arg_1 := _value_i88;
    Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1859 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
      let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
      exact h_5012) (by
      let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
      exact h_5055)), True.intro⟩));
    let _object_w38 := (let _litex_call_arg_0 := _value_i85;
    let _litex_call_arg_1 := _value_i86;
    Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1859 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
      let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
      exact h_5012) (by
      let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
      exact h_5015)), True.intro⟩));
    (let _litex_call_arg_0 := _object_w37;
    let _litex_call_arg_1 := _object_w38;
    Litex.callOn ((_object_i40 (M := M))).val.signature (_object_i40 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_4141 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
      let _atomic_wd_1_0 := _object_w37
      let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
      exact (by
        let _litex_return_call := _object_w37
        exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_1_1 _atomic_wd_1_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_1_1) (Litex.callOnInOutput _litex_return_call))) (by
      let _atomic_wd_1_0 := _object_w38
      let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
      exact (by
        let _litex_return_call := _object_w38
        exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_1_1 _atomic_wd_1_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_1_1) (Litex.callOnInOutput _litex_return_call)))), True.intro⟩))) (Litex.number (M := M) (0 : ℂ))))

    have h_4817 : (by
      let _equal_wd_1_0 := (let _litex_call_arg_0 := _value_i85;
      let _litex_call_arg_1 := _value_i86;
      Litex.callOn ((_object_i77 (M := M))).val.signature (_object_i77 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_4810 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
        let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact h_5012) (by
        let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact h_5015)), (Eq.mpr (congrArg₂ (fun (_raw_i78 : M.Value) (_raw_i79 : M.Value) => (¬ (_raw_i78 = _raw_i79))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) h_4812)⟩))
      let _equal_wd_1_1 := _object_w49
      exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (let _equal_wd_1_0 := (let _litex_call_arg_0 := _value_i85;
            let _litex_call_arg_1 := _value_i86;
            Litex.callOn ((_object_i77 (M := M))).val.signature (_object_i77 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_4810 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
              let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
              exact h_5012) (by
              let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
              exact h_5015)), (Eq.mpr (congrArg₂ (fun (_raw_i78 : M.Value) (_raw_i79 : M.Value) => (¬ (_raw_i78 = _raw_i79))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) h_4812)⟩));
            let _equal_wd_1_1 := _object_w49;
            (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i77 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i85), (Litex.denote _value_i86)])) = (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_raw_i88 : M.Value) => ∃ (_ : M.mem _raw_i88 (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)])), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i40 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i85), _raw_i88])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i85), (Litex.denote _value_i86)]))])) = (M.number (0 : ℂ))))) from by
              have _litex_residual : (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_raw_i80 : M.Value) => ∃ (_ : M.mem _raw_i80 (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)])), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i40 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i85), _raw_i80])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i85), (Litex.denote _value_i86)]))])) = (M.number (0 : ℂ))))) = (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_raw_i88 : M.Value) => ∃ (_ : M.mem _raw_i88 (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)])), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i40 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i85), _raw_i88])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i85), (Litex.denote _value_i86)]))])) = (M.number (0 : ℂ))))) := (let _equal_wd_2_0 := (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) (fun (_value_i80 : Litex.Obj (M := M) M.Value) (h_5273 : Litex.In _value_i80 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) => Litex.Same (let _object_w41 := (let _litex_call_arg_0 := _value_i85;
              let _litex_call_arg_1 := _value_i80;
              Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1859 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                exact h_5012) (by
                let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                exact h_5273)), True.intro⟩));
              let _object_w42 := (let _litex_call_arg_0 := _value_i85;
              let _litex_call_arg_1 := _value_i86;
              Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1859 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                exact h_5012) (by
                let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                exact h_5015)), True.intro⟩));
              (let _litex_call_arg_0 := _object_w41;
              let _litex_call_arg_1 := _object_w42;
              Litex.callOn ((_object_i40 (M := M))).val.signature (_object_i40 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_4141 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                let _atomic_wd_1_0 := _object_w41
                let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                exact (by
                  let _litex_return_call := _object_w41
                  exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_1_1 _atomic_wd_1_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_1_1) (Litex.callOnInOutput _litex_return_call))) (by
                let _atomic_wd_1_0 := _object_w42
                let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                exact (by
                  let _litex_return_call := _object_w42
                  exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_1_1 _atomic_wd_1_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_1_1) (Litex.callOnInOutput _litex_return_call)))), True.intro⟩))) (Litex.number (M := M) (0 : ℂ))));
              let _equal_wd_2_1 := (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) (fun (_value_i88 : Litex.Obj (M := M) M.Value) (h_5456 : Litex.In _value_i88 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) => Litex.Same (let _object_w45 := (let _litex_call_arg_0 := _value_i85;
              let _litex_call_arg_1 := _value_i88;
              Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1859 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                exact h_5012) (by
                let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                exact h_5456)), True.intro⟩));
              let _object_w46 := (let _litex_call_arg_0 := _value_i85;
              let _litex_call_arg_1 := _value_i86;
              Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1859 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                exact h_5012) (by
                let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                exact h_5015)), True.intro⟩));
              (let _litex_call_arg_0 := _object_w45;
              let _litex_call_arg_1 := _object_w46;
              Litex.callOn ((_object_i40 (M := M))).val.signature (_object_i40 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_4141 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                let _atomic_wd_1_0 := _object_w45
                let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                exact (by
                  let _litex_return_call := _object_w45
                  exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_1_1 _atomic_wd_1_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_1_1) (Litex.callOnInOutput _litex_return_call))) (by
                let _atomic_wd_1_0 := _object_w46
                let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                exact (by
                  let _litex_return_call := _object_w46
                  exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_1_1 _atomic_wd_1_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_1_1) (Litex.callOnInOutput _litex_return_call)))), True.intro⟩))) (Litex.number (M := M) (0 : ℂ))));
              (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from rfl)))
              exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i77 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i85), (Litex.denote _value_i86)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i77 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i85), (Litex.denote _value_i86)])) = (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_raw_i80 : M.Value) => ∃ (_ : M.mem _raw_i80 (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)])), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i40 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i85), _raw_i80])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i85), (Litex.denote _value_i86)]))])) = (M.number (0 : ℂ))))) from by
              let _litex_original := _equal_wd_1_0
              let _litex_literal := (let _wd_1_0 := (_object_i77 (M := M));
            let _wd_1_1 := _value_i85;
            let _wd_1_2 := _value_i86;
            (let _litex_call_arg_0 := _wd_1_1;
            let _litex_call_arg_1 := _wd_1_2;
            Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))] (by
              have _finiteProof_0 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
              have _finiteProof_1 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
              exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
            )) (let _wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))));
            (Litex.powerSet _wd_1_0)) (fun (_litex_input : M.Value) => (fun (_raw_i78 : M.Value) (_raw_i79 : M.Value) => (¬ (_raw_i78 = _raw_i79))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _wd_1_0 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.formulaFnInFnSet _wd_1_0) (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
              let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
              exact h_5012) (by
              let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
              exact h_5015)) (Eq.mpr (congrArg₂ (fun (_raw_i78 : M.Value) (_raw_i79 : M.Value) => (¬ (_raw_i78 = _raw_i79))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) h_4812)))
              have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_4811 (M := M)) (Litex.sameRefl _litex_original.val.argument)
              have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
              exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i78 : M.Value) (_raw_i79 : M.Value) => (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_raw_i80 : M.Value) => ∃ (_ : M.mem _raw_i80 (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)])), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i40 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i78, _raw_i80])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i78, _raw_i79]))])) = (M.number (0 : ℂ)))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_raw_i80 : M.Value) => ∃ (_ : M.mem _raw_i80 (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)])), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i40 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i85), _raw_i80])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i85), (Litex.denote _value_i86)]))])) = (M.number (0 : ℂ))))); exact (congrArg₂ (fun (_raw_i78 : M.Value) (_raw_i79 : M.Value) => (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_raw_i80 : M.Value) => ∃ (_ : M.mem _raw_i80 (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)])), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i40 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i78, _raw_i80])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i78, _raw_i79]))])) = (M.number (0 : ℂ)))))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i85), (Litex.denote _value_i86)]) (M.number (1 : ℂ)) = (Litex.denote _value_i85) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i85), (Litex.denote _value_i86)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i85), (Litex.denote _value_i86)]) (M.number (2 : ℂ)) = (Litex.denote _value_i86) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i85), (Litex.denote _value_i86)] (1 : Fin 2)))))
            ))).trans _litex_residual)))
          )
      )
    have h_4818 : (by
      let _atomic_wd_1_1 := (let _litex_call_arg_0 := _value_i85;
      let _litex_call_arg_1 := _value_i86;
      Litex.callOn ((_object_i77 (M := M))).val.signature (_object_i77 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_4810 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
        let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact h_5012) (by
        let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact h_5015)), (Eq.mpr (congrArg₂ (fun (_raw_i78 : M.Value) (_raw_i79 : M.Value) => (¬ (_raw_i78 = _raw_i79))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) h_4812)⟩))
      exact Litex.In _value_i87 _atomic_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _atomic_wd_1_1 := (let _litex_call_arg_0 := _value_i85;
              let _litex_call_arg_1 := _value_i86;
              Litex.callOn ((_object_i77 (M := M))).val.signature (_object_i77 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_4810 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                exact h_5012) (by
                let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                exact h_5015)), (Eq.mpr (congrArg₂ (fun (_raw_i78 : M.Value) (_raw_i79 : M.Value) => (¬ (_raw_i78 = _raw_i79))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) h_4812)⟩))
              exact h_4813)
          )
      )

    have h_5665 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i40 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i85), (Litex.denote _value_i87)])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i85), (Litex.denote _value_i86)]))])) = (M.number (0 : ℂ))) :=
      (by
        litex_checked_step =>
          exact (
            (((Litex.inSetBuilder_iff _value_i87 (_object_w49).val.bound (_object_w49).val.predicate).mp (Litex.inOfSame _value_i87 _value_i87 (let _litex_call_arg_0 := _value_i85;
            let _litex_call_arg_1 := _value_i86;
            Litex.callOn ((_object_i77 (M := M))).val.signature (_object_i77 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_4810 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
              let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
              exact h_5012) (by
              let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
              exact h_5015)), (Eq.mpr (congrArg₂ (fun (_raw_i78 : M.Value) (_raw_i79 : M.Value) => (¬ (_raw_i78 = _raw_i79))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) h_4812)⟩)) _object_w49 (Litex.sameRefl _value_i87) (((Litex.sameRefl (let _litex_call_arg_0 := _value_i85;
            let _litex_call_arg_1 := _value_i86;
            Litex.callOn ((_object_i77 (M := M))).val.signature (_object_i77 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_4810 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
              let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
              exact h_5012) (by
              let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
              exact h_5015)), (Eq.mpr (congrArg₂ (fun (_raw_i78 : M.Value) (_raw_i79 : M.Value) => (¬ (_raw_i78 = _raw_i79))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) h_4812)⟩)))).trans h_4817) h_4818))).choose_spec
          )
      )
    exact h_5665
  )
end LitexCompiled.file_lean_x2f_examples_x2f_line_x5f_membership_x5f_condition_x2f_statement_x2e_lit
