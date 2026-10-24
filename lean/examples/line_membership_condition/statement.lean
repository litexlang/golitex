import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_line_x5f_membership_x5f_condition_x2f_statement_x2e_lit

universe u v21 v22 v23
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
        let _atomic_wd_2_0 := _wd_2_0
        exact (M.real_subset_complex _ h_21)) (by
        let _atomic_wd_2_0 := _wd_2_1
        exact (M.real_subset_complex _ h_18))));
      let _wd_1_1 := (let _wd_2_0 := _object_h22;
      let _wd_2_1 := _object_h19;
      (Litex.sub _wd_2_0 _wd_2_1 (by
        let _atomic_wd_2_0 := _wd_2_0
        exact (M.real_subset_complex _ h_22)) (by
        let _atomic_wd_2_0 := _wd_2_1
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
        let _atomic_wd_2_0 := _wd_2_0
        exact (M.real_subset_complex _ h_21)) (by
        let _atomic_wd_2_0 := _wd_2_1
        exact (M.real_subset_complex _ h_18))));
      let _wd_1_1 := (let _wd_2_0 := _object_h22;
      let _wd_2_1 := _object_h19;
      (Litex.sub _wd_2_0 _wd_2_1 (by
        let _atomic_wd_2_0 := _wd_2_0
        exact (M.real_subset_complex _ h_22)) (by
        let _atomic_wd_2_0 := _wd_2_1
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
        have _checked_header : ∀ (_raw_i6 : M.Value), M.mem _raw_i6 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) → ((fun (_raw_i6 : M.Value) => True) _raw_i6) → True := by
          intro _raw_i6 h_410 _
          let _value_i6 := Litex.semanticObject (M := M) _raw_i6 (M.member_isSet h_410)
          have h_410 : Litex.In _value_i6 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) := h_410
          exact True.intro
        exact Litex.fnSet (Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.denote (Litex.union (Litex.R (M := M)) (Litex.R (M := M)))) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.isSet (Litex.union (Litex.R (M := M)) (Litex.R (M := M)))) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input)))
        let _function := (let _wd_1_0 := (let _wd_2_0 := _object_h21;
      let _wd_2_1 := _object_h18;
      (Litex.sub _wd_2_0 _wd_2_1 (by
        let _atomic_wd_2_0 := _wd_2_0
        exact (M.real_subset_complex _ h_21)) (by
        let _atomic_wd_2_0 := _wd_2_1
        exact (M.real_subset_complex _ h_18))));
      let _wd_1_1 := (let _wd_2_0 := _object_h22;
      let _wd_2_1 := _object_h19;
      (Litex.sub _wd_2_0 _wd_2_1 (by
        let _atomic_wd_2_0 := _wd_2_0
        exact (M.real_subset_complex _ h_22)) (by
        let _atomic_wd_2_0 := _wd_2_1
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
              let _atomic_wd_3_0 := _wd_1_0
              exact (M.real_subset_complex _ h_21)) (by
              let _atomic_wd_3_0 := _wd_1_1
              exact (M.real_subset_complex _ h_18))))
            exact (Litex.subInR (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right h_21 h_18)))
          have _finiteProof_1 := ((by
            let _atomic_wd_2_0 := (let _wd_1_0 := _object_h22;
            let _wd_1_1 := _object_h19;
            (Litex.sub _wd_1_0 _wd_1_1 (by
              let _atomic_wd_3_0 := _wd_1_0
              exact (M.real_subset_complex _ h_22)) (by
              let _atomic_wd_3_0 := _wd_1_1
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
theorem h_611 : Litex.In (_object_i1 (M := M)) (Litex.fnSet ((_object_i1 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i1 (M := M)))
      )
  )
theorem h_612 : Litex.Same (_object_i1 (M := M)) (_object_i1 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i1 (M := M)))
      )
  )

noncomputable def _object_i8 := (Litex.formulaFnOn (Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
  have _finiteProof_1 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (M.subValue (M.mulValue (Litex.FunctionSemantics.callValue (M := M) _raw_i9 (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i10 (M.number (2 : ℂ)))) (M.mulValue (Litex.FunctionSemantics.callValue (M := M) _raw_i9 (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i10 (M.number (1 : ℂ)))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
  have _litex_checked_return : ∀ (_raw_i9 : M.Value) (_raw_i10 : M.Value), M.mem _raw_i9 (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) → M.mem _raw_i10 (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) → ((fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) _raw_i9 _raw_i10) → M.mem ((fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (M.subValue (M.mulValue (Litex.FunctionSemantics.callValue (M := M) _raw_i9 (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i10 (M.number (2 : ℂ)))) (M.mulValue (Litex.FunctionSemantics.callValue (M := M) _raw_i9 (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i10 (M.number (1 : ℂ)))))) _raw_i9 _raw_i10) (Litex.denote (Litex.R (M := M))) := (by
    intro _raw_i9 _raw_i10 h_629 h_632 _
    let _value_i9 := Litex.semanticObject (M := M) _raw_i9 (M.member_isSet h_629)
    have h_629 : Litex.In _value_i9 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) := h_629
    let _object_h630 := (Litex.cartCall _value_i9 _ (Litex.number (M := M) (1 : ℂ)) h_629 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_630 : Litex.In _object_h630 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_629 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h631 := (Litex.cartCall _value_i9 _ (Litex.number (M := M) (2 : ℂ)) h_629 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_631 : Litex.In _object_h631 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_629 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    let _value_i10 := Litex.semanticObject (M := M) _raw_i10 (M.member_isSet h_632)
    have h_632 : Litex.In _value_i10 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) := h_632
    let _object_h633 := (Litex.cartCall _value_i10 _ (Litex.number (M := M) (1 : ℂ)) h_632 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_633 : Litex.In _object_h633 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_632 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h634 := (Litex.cartCall _value_i10 _ (Litex.number (M := M) (2 : ℂ)) h_632 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_634 : Litex.In _object_h634 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_632 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    change (by
      let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := _object_h630;
      let _wd_2_1 := _object_h634;
      (Litex.mul _wd_2_0 _wd_2_1 (by
        let _atomic_wd_2_0 := _wd_2_0
        exact (M.real_subset_complex _ h_630)) (by
        let _atomic_wd_2_0 := _wd_2_1
        exact (M.real_subset_complex _ h_634))));
      let _wd_1_1 := (let _wd_2_0 := _object_h631;
      let _wd_2_1 := _object_h633;
      (Litex.mul _wd_2_0 _wd_2_1 (by
        let _atomic_wd_2_0 := _wd_2_0
        exact (M.real_subset_complex _ h_631)) (by
        let _atomic_wd_2_0 := _wd_2_1
        exact (M.real_subset_complex _ h_633))));
      (Litex.sub _wd_1_0 _wd_1_1 (by
        let _atomic_wd_2_0 := _wd_1_0
        exact (Litex.mulInC (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (M.real_subset_complex _ h_630) (M.real_subset_complex _ h_634))) (by
        let _atomic_wd_2_0 := _wd_1_1
        exact (Litex.mulInC (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (M.real_subset_complex _ h_631) (M.real_subset_complex _ h_633)))))
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := _object_h630;
      let _wd_2_1 := _object_h634;
      (Litex.mul _wd_2_0 _wd_2_1 (by
        let _atomic_wd_2_0 := _wd_2_0
        exact (M.real_subset_complex _ h_630)) (by
        let _atomic_wd_2_0 := _wd_2_1
        exact (M.real_subset_complex _ h_634))));
      let _wd_1_1 := (let _wd_2_0 := _object_h631;
      let _wd_2_1 := _object_h633;
      (Litex.mul _wd_2_0 _wd_2_1 (by
        let _atomic_wd_2_0 := _wd_2_0
        exact (M.real_subset_complex _ h_631)) (by
        let _atomic_wd_2_0 := _wd_2_1
        exact (M.real_subset_complex _ h_633))));
      (Litex.sub _wd_1_0 _wd_1_1 (by
        let _atomic_wd_2_0 := _wd_1_0
        exact (Litex.mulInC (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (M.real_subset_complex _ h_630) (M.real_subset_complex _ h_634))) (by
        let _atomic_wd_2_0 := _wd_1_1
        exact (Litex.mulInC (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (M.real_subset_complex _ h_631) (M.real_subset_complex _ h_633)))))
      exact (Litex.subInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.mulInR ((_atomic_wd_1_0).val.left).val.left ((_atomic_wd_1_0).val.left).val.right h_630 h_634) (Litex.mulInR ((_atomic_wd_1_0).val.right).val.left ((_atomic_wd_1_0).val.right).val.right h_631 h_633))))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
  have _finiteProof_1 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
  exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard))
theorem h_1453 : Litex.In (_object_i8 (M := M)) (Litex.fnSet ((_object_i8 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i8 (M := M)))
      )
  )
theorem h_1454 : Litex.Same (_object_i8 (M := M)) (_object_i8 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i8 (M := M)))
      )
  )

noncomputable def _object_i13 := (Litex.formulaFnOn (Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))]) (Litex.denote (let _wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))));
(Litex.powerSet _wd_1_0))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
  have _finiteProof_1 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet (let _wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))));
(Litex.powerSet _wd_1_0))) (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (¬ (_raw_i14 = _raw_i15))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_raw_i16 : M.Value) => ∃ (_ : M.mem _raw_i16 (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)])), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i14, _raw_i16])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i14, _raw_i15]))])) = (M.number (0 : ℂ)))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
  have _litex_checked_return : ∀ (_raw_i14 : M.Value) (_raw_i15 : M.Value), M.mem _raw_i14 (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) → M.mem _raw_i15 (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) → ((fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (¬ (_raw_i14 = _raw_i15))) _raw_i14 _raw_i15) → M.mem ((fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_raw_i16 : M.Value) => ∃ (_ : M.mem _raw_i16 (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)])), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i14, _raw_i16])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i14, _raw_i15]))])) = (M.number (0 : ℂ)))))) _raw_i14 _raw_i15) (Litex.denote (let _wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))));
(Litex.powerSet _wd_1_0))) := (by
    intro _raw_i14 _raw_i15 h_1503 h_1506 h_1455
    let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_1503)
    have h_1503 : Litex.In _value_i14 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) := h_1503
    let _object_h1504 := (Litex.cartCall _value_i14 _ (Litex.number (M := M) (1 : ℂ)) h_1503 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_1504 : Litex.In _object_h1504 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_1503 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h1505 := (Litex.cartCall _value_i14 _ (Litex.number (M := M) (2 : ℂ)) h_1503 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_1505 : Litex.In _object_h1505 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_1503 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_1506)
    have h_1506 : Litex.In _value_i15 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) := h_1506
    let _object_h1507 := (Litex.cartCall _value_i15 _ (Litex.number (M := M) (1 : ℂ)) h_1506 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_1507 : Litex.In _object_h1507 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_1506 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h1508 := (Litex.cartCall _value_i15 _ (Litex.number (M := M) (2 : ℂ)) h_1506 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_1508 : Litex.In _object_h1508 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_1506 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    have h_1455 : ¬ Litex.Same _value_i14 _value_i15 :=
      (by
        litex_checked_step =>
          exact (
            (by
              change (¬ (_raw_i14 = _raw_i15))
              exact h_1455)
          )
      )
    change (by
      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) (fun (_value_i16 : Litex.Obj (M := M) M.Value) (h_1653 : Litex.In _value_i16 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) => Litex.Same (let _object_w54 := (let _litex_call_arg_0 := _value_i14;
      let _litex_call_arg_1 := _value_i16;
      Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_611 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact h_1503) (by
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact h_1653)), True.intro⟩));
      let _object_w55 := (let _litex_call_arg_0 := _value_i14;
      let _litex_call_arg_1 := _value_i15;
      Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_611 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact h_1503) (by
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact h_1506)), True.intro⟩));
      (let _litex_call_arg_0 := _object_w54;
      let _litex_call_arg_1 := _object_w55;
      Litex.callOn ((_object_i8 (M := M))).val.signature (_object_i8 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1453 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
        let _atomic_wd_2_0 := _object_w54
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact (by
          let _litex_return_call := _object_w54
          exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_2_1 _atomic_wd_2_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_2_1) (Litex.callOnInOutput _litex_return_call))) (by
        let _atomic_wd_2_0 := _object_w55
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact (by
          let _litex_return_call := _object_w55
          exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_2_1 _atomic_wd_2_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_2_1) (Litex.callOnInOutput _litex_return_call)))), True.intro⟩))) (Litex.number (M := M) (0 : ℂ))))
      let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))));
      (Litex.powerSet _wd_1_0))
      exact Litex.In _atomic_wd_1_0 _atomic_wd_1_1)
    exact (by
      let _atomic_wd_1_0 := (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) (fun (_value_i16 : Litex.Obj (M := M) M.Value) (h_1653 : Litex.In _value_i16 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) => Litex.Same (let _object_w54 := (let _litex_call_arg_0 := _value_i14;
      let _litex_call_arg_1 := _value_i16;
      Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_611 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact h_1503) (by
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact h_1653)), True.intro⟩));
      let _object_w55 := (let _litex_call_arg_0 := _value_i14;
      let _litex_call_arg_1 := _value_i15;
      Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_611 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact h_1503) (by
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact h_1506)), True.intro⟩));
      (let _litex_call_arg_0 := _object_w54;
      let _litex_call_arg_1 := _object_w55;
      Litex.callOn ((_object_i8 (M := M))).val.signature (_object_i8 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1453 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
        let _atomic_wd_2_0 := _object_w54
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact (by
          let _litex_return_call := _object_w54
          exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_2_1 _atomic_wd_2_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_2_1) (Litex.callOnInOutput _litex_return_call))) (by
        let _atomic_wd_2_0 := _object_w55
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact (by
          let _litex_return_call := _object_w55
          exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_2_1 _atomic_wd_2_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_2_1) (Litex.callOnInOutput _litex_return_call)))), True.intro⟩))) (Litex.number (M := M) (0 : ℂ))))
      let _atomic_wd_1_1 := (let _wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))));
      (Litex.powerSet _wd_1_0))
      exact ((Litex.inPowerSet_iff _atomic_wd_1_0 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))).mpr (by
        let _atomic_wd_2_0 := (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) (fun (_value_i16 : Litex.Obj (M := M) M.Value) (h_1973 : Litex.In _value_i16 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) => Litex.Same (let _object_w66 := (let _litex_call_arg_0 := _value_i14;
        let _litex_call_arg_1 := _value_i16;
        Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_611 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
          let _atomic_wd_3_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
          exact h_1503) (by
          let _atomic_wd_3_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
          exact h_1973)), True.intro⟩));
        let _object_w67 := (let _litex_call_arg_0 := _value_i14;
        let _litex_call_arg_1 := _value_i15;
        Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_611 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
          let _atomic_wd_3_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
          exact h_1503) (by
          let _atomic_wd_3_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
          exact h_1506)), True.intro⟩));
        (let _litex_call_arg_0 := _object_w66;
        let _litex_call_arg_1 := _object_w67;
        Litex.callOn ((_object_i8 (M := M))).val.signature (_object_i8 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1453 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
          let _atomic_wd_3_0 := _object_w66
          let _atomic_wd_3_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
          exact (by
            let _litex_return_call := _object_w66
            exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_3_1 _atomic_wd_3_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_3_1) (Litex.callOnInOutput _litex_return_call))) (by
          let _atomic_wd_3_0 := _object_w67
          let _atomic_wd_3_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
          exact (by
            let _litex_return_call := _object_w67
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
(Litex.powerSet _wd_1_0))) (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (¬ (_raw_i14 = _raw_i15))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
  exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard))
theorem h_2122 : Litex.In (_object_i13 (M := M)) (Litex.fnSet ((_object_i13 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i13 (M := M)))
      )
  )
theorem h_2123 : Litex.Same (_object_i13 (M := M)) (_object_i13 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i13 (M := M)))
      )
  )

theorem h_2127 : ∀ {_Host_i21 : Type v21} [_rep_i21 : Litex.Representation M _Host_i21] (_value_i21 : Litex.Obj (M := M) _Host_i21) (h_2131 : Litex.In _value_i21 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) {_Host_i22 : Type v22} [_rep_i22 : Litex.Representation M _Host_i22] (_value_i22 : Litex.Obj (M := M) _Host_i22) (h_2134 : Litex.In _value_i22 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) {_Host_i23 : Type v23} [_rep_i23 : Litex.Representation M _Host_i23] (_value_i23 : Litex.Obj (M := M) _Host_i23) (h_2137 : Litex.In _value_i23 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) (h_2124 : ¬ Litex.Same _value_i21 _value_i22) (h_2125 : (by
  let _atomic_wd_1_1 := (let _litex_call_arg_0 := _value_i21;
  let _litex_call_arg_1 := _value_i22;
  Litex.callOn ((_object_i13 (M := M))).val.signature (_object_i13 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_2122 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
    exact h_2131) (by
    let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
    exact h_2134)), (Eq.mpr (congrArg₂ (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (¬ (_raw_i14 = _raw_i15))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) h_2124)⟩))
  exact Litex.In _value_i23 _atomic_wd_1_1)), (by
  let _equal_wd_1_0 := (let _object_w87 := (let _litex_call_arg_0 := _value_i21;
  let _litex_call_arg_1 := _value_i23;
  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_611 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
    exact h_2131) (by
    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
    exact h_2137)), True.intro⟩));
  let _object_w88 := (let _litex_call_arg_0 := _value_i21;
  let _litex_call_arg_1 := _value_i22;
  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_611 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
    exact h_2131) (by
    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
    exact h_2134)), True.intro⟩));
  (let _litex_call_arg_0 := _object_w87;
  let _litex_call_arg_1 := _object_w88;
  Litex.callOn ((_object_i8 (M := M))).val.signature (_object_i8 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1453 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_0 := _object_w87
    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
    exact (by
      let _litex_return_call := _object_w87
      exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_1_1 _atomic_wd_1_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_1_1) (Litex.callOnInOutput _litex_return_call))) (by
    let _atomic_wd_1_0 := _object_w88
    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
    exact (by
      let _litex_return_call := _object_w88
      exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_1_1 _atomic_wd_1_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_1_1) (Litex.callOnInOutput _litex_return_call)))), True.intro⟩)))
  exact Litex.Same _equal_wd_1_0 (Litex.number (M := M) (0 : ℂ))) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i21 _rep_i21 _value_i21 h_2131 _Host_i22 _rep_i22 _value_i22 h_2134 _Host_i23 _rep_i23 _value_i23 h_2137 h_2124 h_2125
          let _object_h2132 := (Litex.cartCall _value_i21 _ (Litex.number (M := M) (1 : ℂ)) h_2131 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_2132 : Litex.In _object_h2132 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_2131 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h2133 := (Litex.cartCall _value_i21 _ (Litex.number (M := M) (2 : ℂ)) h_2131 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_2133 : Litex.In _object_h2133 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_2131 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          let _object_h2135 := (Litex.cartCall _value_i22 _ (Litex.number (M := M) (1 : ℂ)) h_2134 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_2135 : Litex.In _object_h2135 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_2134 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h2136 := (Litex.cartCall _value_i22 _ (Litex.number (M := M) (2 : ℂ)) h_2134 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_2136 : Litex.In _object_h2136 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_2134 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          let _object_h2138 := (Litex.cartCall _value_i23 _ (Litex.number (M := M) (1 : ℂ)) h_2137 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_2138 : Litex.In _object_h2138 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_2137 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h2139 := (Litex.cartCall _value_i23 _ (Litex.number (M := M) (2 : ℂ)) h_2137 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_2139 : Litex.In _object_h2139 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_2137 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_2324 : Litex.In _value_i21 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_2131
                )
            )
          have h_2327 : Litex.In _value_i22 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_2134
                )
            )
          have h_2330 : Litex.In _value_i23 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_2137
                )
            )
          let _object_h2325 := (Litex.cartCall _value_i21 _ (Litex.number (M := M) (1 : ℂ)) h_2324 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_2325 : Litex.In _object_h2325 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_2324 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h2326 := (Litex.cartCall _value_i21 _ (Litex.number (M := M) (2 : ℂ)) h_2324 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_2326 : Litex.In _object_h2326 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_2324 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          let _object_h2328 := (Litex.cartCall _value_i22 _ (Litex.number (M := M) (1 : ℂ)) h_2327 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_2328 : Litex.In _object_h2328 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_2327 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h2329 := (Litex.cartCall _value_i22 _ (Litex.number (M := M) (2 : ℂ)) h_2327 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_2329 : Litex.In _object_h2329 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_2327 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          let _object_h2331 := (Litex.cartCall _value_i23 _ (Litex.number (M := M) (1 : ℂ)) h_2330 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_2331 : Litex.In _object_h2331 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_2330 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h2332 := (Litex.cartCall _value_i23 _ (Litex.number (M := M) (2 : ℂ)) h_2330 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_2332 : Litex.In _object_h2332 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_2330 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          let _object_w116 := (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) (fun (_value_i24 : Litex.Obj (M := M) M.Value) (h_2367 : Litex.In _value_i24 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) => Litex.Same (let _object_w100 := (let _litex_call_arg_0 := _value_i21;
          let _litex_call_arg_1 := _value_i24;
          Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_611 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
            exact h_2324) (by
            let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
            exact h_2367)), True.intro⟩));
          let _object_w101 := (let _litex_call_arg_0 := _value_i21;
          let _litex_call_arg_1 := _value_i22;
          Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_611 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
            exact h_2324) (by
            let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
            exact h_2327)), True.intro⟩));
          (let _litex_call_arg_0 := _object_w100;
          let _litex_call_arg_1 := _object_w101;
          Litex.callOn ((_object_i8 (M := M))).val.signature (_object_i8 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1453 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_0 := _object_w100
            let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
            exact (by
              let _litex_return_call := _object_w100
              exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_1_1 _atomic_wd_1_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_1_1) (Litex.callOnInOutput _litex_return_call))) (by
            let _atomic_wd_1_0 := _object_w101
            let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
            exact (by
              let _litex_return_call := _object_w101
              exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_1_1 _atomic_wd_1_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_1_1) (Litex.callOnInOutput _litex_return_call)))), True.intro⟩))) (Litex.number (M := M) (0 : ℂ))))

          have h_2129 : (by
            let _equal_wd_1_0 := (let _litex_call_arg_0 := _value_i21;
            let _litex_call_arg_1 := _value_i22;
            Litex.callOn ((_object_i13 (M := M))).val.signature (_object_i13 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_2122 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
              let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
              exact h_2324) (by
              let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
              exact h_2327)), (Eq.mpr (congrArg₂ (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (¬ (_raw_i14 = _raw_i15))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) h_2124)⟩))
            let _equal_wd_1_1 := _object_w116
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := (let _litex_call_arg_0 := _value_i21;
                  let _litex_call_arg_1 := _value_i22;
                  Litex.callOn ((_object_i13 (M := M))).val.signature (_object_i13 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_2122 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2324) (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2327)), (Eq.mpr (congrArg₂ (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (¬ (_raw_i14 = _raw_i15))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) h_2124)⟩));
                  let _equal_wd_1_1 := _object_w116;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i13 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i21), (Litex.denote _value_i22)])) = (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_raw_i24 : M.Value) => ∃ (_ : M.mem _raw_i24 (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)])), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i21), _raw_i24])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i21), (Litex.denote _value_i22)]))])) = (M.number (0 : ℂ))))) from by
                    have _litex_residual : (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_raw_i16 : M.Value) => ∃ (_ : M.mem _raw_i16 (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)])), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i21), _raw_i16])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i21), (Litex.denote _value_i22)]))])) = (M.number (0 : ℂ))))) = (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_raw_i24 : M.Value) => ∃ (_ : M.mem _raw_i24 (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)])), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i21), _raw_i24])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i21), (Litex.denote _value_i22)]))])) = (M.number (0 : ℂ))))) := (let _equal_wd_2_0 := (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) (fun (_value_i16 : Litex.Obj (M := M) M.Value) (h_2585 : Litex.In _value_i16 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) => Litex.Same (let _object_w106 := (let _litex_call_arg_0 := _value_i21;
                    let _litex_call_arg_1 := _value_i16;
                    Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_611 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                      let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                      exact h_2324) (by
                      let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                      exact h_2585)), True.intro⟩));
                    let _object_w107 := (let _litex_call_arg_0 := _value_i21;
                    let _litex_call_arg_1 := _value_i22;
                    Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_611 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                      let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                      exact h_2324) (by
                      let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                      exact h_2327)), True.intro⟩));
                    (let _litex_call_arg_0 := _object_w106;
                    let _litex_call_arg_1 := _object_w107;
                    Litex.callOn ((_object_i8 (M := M))).val.signature (_object_i8 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1453 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                      let _atomic_wd_1_0 := _object_w106
                      let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                      exact (by
                        let _litex_return_call := _object_w106
                        exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_1_1 _atomic_wd_1_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_1_1) (Litex.callOnInOutput _litex_return_call))) (by
                      let _atomic_wd_1_0 := _object_w107
                      let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                      exact (by
                        let _litex_return_call := _object_w107
                        exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_1_1 _atomic_wd_1_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_1_1) (Litex.callOnInOutput _litex_return_call)))), True.intro⟩))) (Litex.number (M := M) (0 : ℂ))));
                    let _equal_wd_2_1 := (Litex.setBuilder (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) (fun (_value_i24 : Litex.Obj (M := M) M.Value) (h_2768 : Litex.In _value_i24 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) => Litex.Same (let _object_w112 := (let _litex_call_arg_0 := _value_i21;
                    let _litex_call_arg_1 := _value_i24;
                    Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_611 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                      let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                      exact h_2324) (by
                      let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                      exact h_2768)), True.intro⟩));
                    let _object_w113 := (let _litex_call_arg_0 := _value_i21;
                    let _litex_call_arg_1 := _value_i22;
                    Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_611 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                      let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                      exact h_2324) (by
                      let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                      exact h_2327)), True.intro⟩));
                    (let _litex_call_arg_0 := _object_w112;
                    let _litex_call_arg_1 := _object_w113;
                    Litex.callOn ((_object_i8 (M := M))).val.signature (_object_i8 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1453 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                      let _atomic_wd_1_0 := _object_w112
                      let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                      exact (by
                        let _litex_return_call := _object_w112
                        exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_1_1 _atomic_wd_1_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_1_1) (Litex.callOnInOutput _litex_return_call))) (by
                      let _atomic_wd_1_0 := _object_w113
                      let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                      exact (by
                        let _litex_return_call := _object_w113
                        exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_1_1 _atomic_wd_1_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_1_1) (Litex.callOnInOutput _litex_return_call)))), True.intro⟩))) (Litex.number (M := M) (0 : ℂ))));
                    (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from rfl)))
                    exact ((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i13 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i21), (Litex.denote _value_i22)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i13 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i21), (Litex.denote _value_i22)])) = (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_raw_i16 : M.Value) => ∃ (_ : M.mem _raw_i16 (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)])), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i21), _raw_i16])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i21), (Litex.denote _value_i22)]))])) = (M.number (0 : ℂ))))) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i13 (M := M));
                  let _wd_1_1 := _value_i21;
                  let _wd_1_2 := _value_i22;
                  (let _litex_call_arg_0 := _wd_1_1;
                  let _litex_call_arg_1 := _wd_1_2;
                  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
                    have _finiteProof_1 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (let _wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))));
                  (Litex.powerSet _wd_1_0)) (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (¬ (_raw_i14 = _raw_i15))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _wd_1_0 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.formulaFnInFnSet _wd_1_0) (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2324) (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2327)) (Eq.mpr (congrArg₂ (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (¬ (_raw_i14 = _raw_i15))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) h_2124)))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_2123 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_raw_i16 : M.Value) => ∃ (_ : M.mem _raw_i16 (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)])), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i14, _raw_i16])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i14, _raw_i15]))])) = (M.number (0 : ℂ)))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_raw_i16 : M.Value) => ∃ (_ : M.mem _raw_i16 (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)])), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i21), _raw_i16])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i21), (Litex.denote _value_i22)]))])) = (M.number (0 : ℂ))))); exact (congrArg₂ (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (Litex.SetSemantics.sepValue (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)]) (fun (_raw_i16 : M.Value) => ∃ (_ : M.mem _raw_i16 (Litex.FiniteFunction.cartValue (M := M) ![(M.standard Litex.StandardSetValue.real), (M.standard Litex.StandardSetValue.real)])), ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i14, _raw_i16])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i14, _raw_i15]))])) = (M.number (0 : ℂ)))))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i21), (Litex.denote _value_i22)]) (M.number (1 : ℂ)) = (Litex.denote _value_i21) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i21), (Litex.denote _value_i22)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i21), (Litex.denote _value_i22)]) (M.number (2 : ℂ)) = (Litex.denote _value_i22) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i21), (Litex.denote _value_i22)] (1 : Fin 2)))))
                  ))).trans _litex_residual)))
                )
            )
          have h_2130 : (by
            let _atomic_wd_1_1 := (let _litex_call_arg_0 := _value_i21;
            let _litex_call_arg_1 := _value_i22;
            Litex.callOn ((_object_i13 (M := M))).val.signature (_object_i13 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_2122 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
              let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
              exact h_2324) (by
              let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
              exact h_2327)), (Eq.mpr (congrArg₂ (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (¬ (_raw_i14 = _raw_i15))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) h_2124)⟩))
            exact Litex.In _value_i23 _atomic_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (by
                    let _atomic_wd_1_1 := (let _litex_call_arg_0 := _value_i21;
                    let _litex_call_arg_1 := _value_i22;
                    Litex.callOn ((_object_i13 (M := M))).val.signature (_object_i13 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_2122 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                      let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                      exact h_2324) (by
                      let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                      exact h_2327)), (Eq.mpr (congrArg₂ (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (¬ (_raw_i14 = _raw_i15))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) h_2124)⟩))
                    exact h_2125)
                )
            )

          have h_2977 : ((Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i21), (Litex.denote _value_i23)])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i21), (Litex.denote _value_i22)]))])) = (M.number (0 : ℂ))) :=
            (by
              litex_checked_step =>
                exact (
                  (((Litex.inSetBuilder_iff _value_i23 (_object_w116).val.bound (_object_w116).val.predicate).mp (Litex.inOfSame _value_i23 _value_i23 (let _litex_call_arg_0 := _value_i21;
                  let _litex_call_arg_1 := _value_i22;
                  Litex.callOn ((_object_i13 (M := M))).val.signature (_object_i13 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_2122 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2324) (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2327)), (Eq.mpr (congrArg₂ (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (¬ (_raw_i14 = _raw_i15))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) h_2124)⟩)) _object_w116 (Litex.sameRefl _value_i23) (((Litex.sameRefl (let _litex_call_arg_0 := _value_i21;
                  let _litex_call_arg_1 := _value_i22;
                  Litex.callOn ((_object_i13 (M := M))).val.signature (_object_i13 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_2122 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2324) (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2327)), (Eq.mpr (congrArg₂ (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (¬ (_raw_i14 = _raw_i15))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (1 : ℂ)) = (Litex.denote _litex_call_arg_0) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)]) (M.number (2 : ℂ)) = (Litex.denote _litex_call_arg_1) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _litex_call_arg_0), (Litex.denote _litex_call_arg_1)] (1 : Fin 2))) h_2124)⟩)))).trans h_2129) h_2130))).choose_spec
                )
            )
          exact h_2977
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_line_x5f_membership_x5f_condition_x2f_statement_x2e_lit
