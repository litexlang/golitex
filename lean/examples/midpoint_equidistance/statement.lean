import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_midpoint_x5f_equidistance_x2f_statement_x2e_lit

universe u v18 v19 v20 v22 v23 v24
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
)) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (M.addValue (M.mulValue (Litex.FunctionSemantics.callValue (M := M) _raw_i9 (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i10 (M.number (1 : ℂ)))) (M.mulValue (Litex.FunctionSemantics.callValue (M := M) _raw_i9 (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i10 (M.number (2 : ℂ)))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
  have _litex_checked_return : ∀ (_raw_i9 : M.Value) (_raw_i10 : M.Value), M.mem _raw_i9 (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) → M.mem _raw_i10 (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) → ((fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) _raw_i9 _raw_i10) → M.mem ((fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (M.addValue (M.mulValue (Litex.FunctionSemantics.callValue (M := M) _raw_i9 (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i10 (M.number (1 : ℂ)))) (M.mulValue (Litex.FunctionSemantics.callValue (M := M) _raw_i9 (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i10 (M.number (2 : ℂ)))))) _raw_i9 _raw_i10) (Litex.denote (Litex.R (M := M))) := (by
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
      let _wd_2_1 := _object_h633;
      (Litex.mul _wd_2_0 _wd_2_1 (by
        let _atomic_wd_2_0 := _wd_2_0
        exact (M.real_subset_complex _ h_630)) (by
        let _atomic_wd_2_0 := _wd_2_1
        exact (M.real_subset_complex _ h_633))));
      let _wd_1_1 := (let _wd_2_0 := _object_h631;
      let _wd_2_1 := _object_h634;
      (Litex.mul _wd_2_0 _wd_2_1 (by
        let _atomic_wd_2_0 := _wd_2_0
        exact (M.real_subset_complex _ h_631)) (by
        let _atomic_wd_2_0 := _wd_2_1
        exact (M.real_subset_complex _ h_634))));
      (Litex.add _wd_1_0 _wd_1_1 (by
        let _atomic_wd_2_0 := _wd_1_0
        exact (Litex.mulInC (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (M.real_subset_complex _ h_630) (M.real_subset_complex _ h_633))) (by
        let _atomic_wd_2_0 := _wd_1_1
        exact (Litex.mulInC (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (M.real_subset_complex _ h_631) (M.real_subset_complex _ h_634)))))
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (let _wd_1_0 := (let _wd_2_0 := _object_h630;
      let _wd_2_1 := _object_h633;
      (Litex.mul _wd_2_0 _wd_2_1 (by
        let _atomic_wd_2_0 := _wd_2_0
        exact (M.real_subset_complex _ h_630)) (by
        let _atomic_wd_2_0 := _wd_2_1
        exact (M.real_subset_complex _ h_633))));
      let _wd_1_1 := (let _wd_2_0 := _object_h631;
      let _wd_2_1 := _object_h634;
      (Litex.mul _wd_2_0 _wd_2_1 (by
        let _atomic_wd_2_0 := _wd_2_0
        exact (M.real_subset_complex _ h_631)) (by
        let _atomic_wd_2_0 := _wd_2_1
        exact (M.real_subset_complex _ h_634))));
      (Litex.add _wd_1_0 _wd_1_1 (by
        let _atomic_wd_2_0 := _wd_1_0
        exact (Litex.mulInC (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (M.real_subset_complex _ h_630) (M.real_subset_complex _ h_633))) (by
        let _atomic_wd_2_0 := _wd_1_1
        exact (Litex.mulInC (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right (M.real_subset_complex _ h_631) (M.real_subset_complex _ h_634)))))
      exact (Litex.addInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.mulInR ((_atomic_wd_1_0).val.left).val.left ((_atomic_wd_1_0).val.left).val.right h_630 h_633) (Litex.mulInR ((_atomic_wd_1_0).val.right).val.left ((_atomic_wd_1_0).val.right).val.right h_631 h_634))))
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

noncomputable def _object_i13 := (Litex.formulaFnOn (Litex.FunctionSignature.withGuard (M := M) (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
  have _finiteProof_1 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))))) (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i14, _raw_i15])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i14, _raw_i15]))]))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (by
  have _litex_checked_return : ∀ (_raw_i14 : M.Value) (_raw_i15 : M.Value), M.mem _raw_i14 (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) → M.mem _raw_i15 (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) → ((fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) _raw_i14 _raw_i15) → M.mem ((fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i14, _raw_i15])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i14, _raw_i15]))]))) _raw_i14 _raw_i15) (Litex.denote (Litex.R (M := M))) := (by
    intro _raw_i14 _raw_i15 h_1471 h_1474 _
    let _value_i14 := Litex.semanticObject (M := M) _raw_i14 (M.member_isSet h_1471)
    have h_1471 : Litex.In _value_i14 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) := h_1471
    let _object_h1472 := (Litex.cartCall _value_i14 _ (Litex.number (M := M) (1 : ℂ)) h_1471 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_1472 : Litex.In _object_h1472 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_1471 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h1473 := (Litex.cartCall _value_i14 _ (Litex.number (M := M) (2 : ℂ)) h_1471 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_1473 : Litex.In _object_h1473 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_1471 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    let _value_i15 := Litex.semanticObject (M := M) _raw_i15 (M.member_isSet h_1474)
    have h_1474 : Litex.In _value_i15 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) := h_1474
    let _object_h1475 := (Litex.cartCall _value_i15 _ (Litex.number (M := M) (1 : ℂ)) h_1474 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_1475 : Litex.In _object_h1475 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_1474 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h1476 := (Litex.cartCall _value_i15 _ (Litex.number (M := M) (2 : ℂ)) h_1474 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_1476 : Litex.In _object_h1476 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_1474 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    change (by
      let _atomic_wd_1_0 := (let _object_w41 := (let _litex_call_arg_0 := _value_i14;
      let _litex_call_arg_1 := _value_i15;
      Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_611 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact h_1471) (by
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact h_1474)), True.intro⟩));
      let _wd_1_1 := _object_w41;
      (let _litex_call_arg_0 := _object_w41;
      let _litex_call_arg_1 := _wd_1_1;
      Litex.callOn ((_object_i8 (M := M))).val.signature (_object_i8 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1453 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
        let _atomic_wd_2_0 := _object_w41
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact (by
          let _litex_return_call := _object_w41
          exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_2_1 _atomic_wd_2_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_2_1) (Litex.callOnInOutput _litex_return_call))) (by
        let _atomic_wd_2_0 := _object_w41
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact (by
          let _litex_return_call := _object_w41
          exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_2_1 _atomic_wd_2_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_2_1) (Litex.callOnInOutput _litex_return_call)))), True.intro⟩)))
      exact Litex.In _atomic_wd_1_0 (Litex.R (M := M)))
    exact (by
      let _atomic_wd_1_0 := (let _object_w41 := (let _litex_call_arg_0 := _value_i14;
      let _litex_call_arg_1 := _value_i15;
      Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_611 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact h_1471) (by
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact h_1474)), True.intro⟩));
      let _wd_1_1 := _object_w41;
      (let _litex_call_arg_0 := _object_w41;
      let _litex_call_arg_1 := _wd_1_1;
      Litex.callOn ((_object_i8 (M := M))).val.signature (_object_i8 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1453 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
        let _atomic_wd_2_0 := _object_w41
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact (by
          let _litex_return_call := _object_w41
          exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_2_1 _atomic_wd_2_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_2_1) (Litex.callOnInOutput _litex_return_call))) (by
        let _atomic_wd_2_0 := _object_w41
        let _atomic_wd_2_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
        exact (by
          let _litex_return_call := _object_w41
          exact Litex.inOfSame _litex_return_call _litex_return_call _atomic_wd_2_1 _atomic_wd_2_1 (Litex.sameRefl _litex_return_call) (Litex.sameRefl _atomic_wd_2_1) (Litex.callOnInOutput _litex_return_call)))), True.intro⟩)))
      exact (by
        let _litex_return_call := _atomic_wd_1_0
        exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.R (M := M)) (Litex.R (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.R (M := M))) (Litex.callOnInOutput _litex_return_call))))
  intro _litex_input _litex_domain
  obtain ⟨_litex_members, _litex_guard⟩ := (Litex.FunctionSignature.withGuard_domain (Litex.FiniteFunction.cartValue (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))]) (Litex.denote (Litex.R (M := M))) (Litex.FiniteFunction.cart_isSet (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))] (by
  have _finiteProof_0 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
  have _finiteProof_1 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
  exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
)) (Litex.isSet (Litex.R (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _litex_input).mp _litex_domain
  exact _litex_checked_return (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ))) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (0 : Fin 2)) (by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _litex_members (1 : Fin 2)) _litex_guard))
theorem h_1820 : Litex.In (_object_i13 (M := M)) (Litex.fnSet ((_object_i13 (M := M))).val.signature) :=
  (by
    litex_complete =>
      exact (
        (Litex.formulaFnInFnSet (_object_i13 (M := M)))
      )
  )
theorem h_1821 : Litex.Same (_object_i13 (M := M)) (_object_i13 (M := M)) :=
  (by
    litex_complete =>
      exact (
        (Litex.sameRefl (_object_i13 (M := M)))
      )
  )

def prop_4 {_Host_i18 : Type v18} [_rep_i18 : Litex.Representation M _Host_i18] (_value_i18 : Litex.Obj (M := M) _Host_i18) {_Host_i19 : Type v19} [_rep_i19 : Litex.Representation M _Host_i19] (_value_i19 : Litex.Obj (M := M) _Host_i19) {_Host_i20 : Type v20} [_rep_i20 : Litex.Representation M _Host_i20] (_value_i20 : Litex.Obj (M := M) _Host_i20) : Prop :=
  ∃ (h_1824 : Litex.In _value_i18 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), ∃ (h_1827 : Litex.In _value_i19 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), ∃ (h_1830 : Litex.In _value_i20 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (by
    let _object_h1825 := (Litex.cartCall _value_i18 _ (Litex.number (M := M) (1 : ℂ)) h_1824 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    let _object_h1826 := (Litex.cartCall _value_i18 _ (Litex.number (M := M) (2 : ℂ)) h_1824 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    let _object_h1828 := (Litex.cartCall _value_i19 _ (Litex.number (M := M) (1 : ℂ)) h_1827 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_1828 : Litex.In _object_h1828 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_1827 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h1829 := (Litex.cartCall _value_i19 _ (Litex.number (M := M) (2 : ℂ)) h_1827 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_1829 : Litex.In _object_h1829 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_1827 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    let _object_h1831 := (Litex.cartCall _value_i20 _ (Litex.number (M := M) (1 : ℂ)) h_1830 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_1831 : Litex.In _object_h1831 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_1830 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h1832 := (Litex.cartCall _value_i20 _ (Litex.number (M := M) (2 : ℂ)) h_1830 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_1832 : Litex.In _object_h1832 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_1830 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    exact (by
      let _object_w58 := (let _wd_1_0 := (let _wd_2_0 := _object_h1828;
      let _wd_2_1 := _object_h1831;
      (Litex.add _wd_2_0 _wd_2_1 (by
        let _atomic_wd_1_0 := _wd_2_0
        exact (M.real_subset_complex _ h_1828)) (by
        let _atomic_wd_1_0 := _wd_2_1
        exact (M.real_subset_complex _ h_1831))));
      let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
      (Litex.div _wd_1_0 _wd_1_1 (by
        let _atomic_wd_1_0 := _wd_1_0
        exact (Litex.addInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (M.real_subset_complex _ h_1828) (M.real_subset_complex _ h_1831))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
      exact ∃ (h_1822 : Litex.Same _object_h1825 _object_w58), (by
        let _object_w59 := (let _wd_1_0 := (let _wd_2_0 := _object_h1829;
        let _wd_2_1 := _object_h1832;
        (Litex.add _wd_2_0 _wd_2_1 (by
          let _atomic_wd_1_0 := _wd_2_0
          exact (M.real_subset_complex _ h_1829)) (by
          let _atomic_wd_1_0 := _wd_2_1
          exact (M.real_subset_complex _ h_1832))));
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.div _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := _wd_1_0
          exact (Litex.addInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (M.real_subset_complex _ h_1829) (M.real_subset_complex _ h_1832))) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber _wd_1_1 (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))))
        exact Litex.Same _object_h1826 _object_w59
      )
    )
  )

theorem h_2468 : ∀ {_Host_i22 : Type v22} [_rep_i22 : Litex.Representation M _Host_i22] (_value_i22 : Litex.Obj (M := M) _Host_i22) (h_2477 : Litex.In _value_i22 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) {_Host_i23 : Type v23} [_rep_i23 : Litex.Representation M _Host_i23] (_value_i23 : Litex.Obj (M := M) _Host_i23) (h_2480 : Litex.In _value_i23 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) {_Host_i24 : Type v24} [_rep_i24 : Litex.Representation M _Host_i24] (_value_i24 : Litex.Obj (M := M) _Host_i24) (h_2483 : Litex.In _value_i24 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))) (h_2465 : ¬ Litex.Same _value_i22 _value_i23) (h_2466 : ((prop_4 (M := M)) _value_i24 _value_i22 _value_i23)), (by
  let _equal_wd_1_0 := (let _litex_call_arg_0 := _value_i22;
  let _litex_call_arg_1 := _value_i24;
  Litex.callOn ((_object_i13 (M := M))).val.signature (_object_i13 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1820 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
    exact h_2477) (by
    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
    exact h_2483)), True.intro⟩))
  let _equal_wd_1_1 := (let _litex_call_arg_0 := _value_i23;
  let _litex_call_arg_1 := _value_i24;
  Litex.callOn ((_object_i13 (M := M))).val.signature (_object_i13 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1820 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
    exact h_2480) (by
    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
    exact h_2483)), True.intro⟩))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i22 _rep_i22 _value_i22 h_2477 _Host_i23 _rep_i23 _value_i23 h_2480 _Host_i24 _rep_i24 _value_i24 h_2483 h_2465 h_2466
          let _object_h2478 := (Litex.cartCall _value_i22 _ (Litex.number (M := M) (1 : ℂ)) h_2477 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_2478 : Litex.In _object_h2478 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_2477 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h2479 := (Litex.cartCall _value_i22 _ (Litex.number (M := M) (2 : ℂ)) h_2477 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_2479 : Litex.In _object_h2479 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_2477 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          let _object_h2481 := (Litex.cartCall _value_i23 _ (Litex.number (M := M) (1 : ℂ)) h_2480 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_2481 : Litex.In _object_h2481 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_2480 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h2482 := (Litex.cartCall _value_i23 _ (Litex.number (M := M) (2 : ℂ)) h_2480 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_2482 : Litex.In _object_h2482 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_2480 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          let _object_h2484 := (Litex.cartCall _value_i24 _ (Litex.number (M := M) (1 : ℂ)) h_2483 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_2484 : Litex.In _object_h2484 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_2483 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h2485 := (Litex.cartCall _value_i24 _ (Litex.number (M := M) (2 : ℂ)) h_2483 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_2485 : Litex.In _object_h2485 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_2483 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_2486 :=
            (Classical.choose (show ((prop_4 (M := M)) _value_i24 _value_i22 _value_i23) from h_2466))
          have h_2487 :=
            (Classical.choose (Classical.choose_spec (show ((prop_4 (M := M)) _value_i24 _value_i22 _value_i23) from h_2466)))
          have h_2488 :=
            (Classical.choose (Classical.choose_spec (Classical.choose_spec (show ((prop_4 (M := M)) _value_i24 _value_i22 _value_i23) from h_2466))))
          have h_2489 :=
            (Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (show ((prop_4 (M := M)) _value_i24 _value_i22 _value_i23) from h_2466)))))
          have h_2490 :=
            (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (show ((prop_4 (M := M)) _value_i24 _value_i22 _value_i23) from h_2466)))))
          have h_2541 : Litex.In _value_i22 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_2477
                )
            )
          have h_2544 : Litex.In _value_i23 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_2480
                )
            )
          have h_2547 : Litex.In _value_i24 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) :=
            (by
              litex_checked_step =>
                exact (
                  h_2483
                )
            )
          let _object_h2542 := (Litex.cartCall _value_i22 _ (Litex.number (M := M) (1 : ℂ)) h_2541 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_2542 : Litex.In _object_h2542 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_2541 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h2543 := (Litex.cartCall _value_i22 _ (Litex.number (M := M) (2 : ℂ)) h_2541 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_2543 : Litex.In _object_h2543 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_2541 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          let _object_h2545 := (Litex.cartCall _value_i23 _ (Litex.number (M := M) (1 : ℂ)) h_2544 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_2545 : Litex.In _object_h2545 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_2544 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h2546 := (Litex.cartCall _value_i23 _ (Litex.number (M := M) (2 : ℂ)) h_2544 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_2546 : Litex.In _object_h2546 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_2544 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          let _object_h2548 := (Litex.cartCall _value_i24 _ (Litex.number (M := M) (1 : ℂ)) h_2547 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
          have h_2548 : Litex.In _object_h2548 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_2547 (0 : Fin 2) (1 : ℂ) (by norm_num))
                )
            )
          let _object_h2549 := (Litex.cartCall _value_i24 _ (Litex.number (M := M) (2 : ℂ)) h_2547 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
          have h_2549 : Litex.In _object_h2549 (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.FiniteFunction.coordinate_mem_number (M := M) h_2547 (1 : Fin 2) (2 : ℂ) (by norm_num))
                )
            )
          have h_2550 :=
            (Classical.choose (show ((prop_4 (M := M)) _value_i24 _value_i22 _value_i23) from h_2466))
          have h_2551 :=
            (Classical.choose (Classical.choose_spec (show ((prop_4 (M := M)) _value_i24 _value_i22 _value_i23) from h_2466)))
          have h_2552 :=
            (Classical.choose (Classical.choose_spec (Classical.choose_spec (show ((prop_4 (M := M)) _value_i24 _value_i22 _value_i23) from h_2466))))
          have h_2553 :=
            (Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (show ((prop_4 (M := M)) _value_i24 _value_i22 _value_i23) from h_2466)))))
          have h_2554 :=
            (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (show ((prop_4 (M := M)) _value_i24 _value_i22 _value_i23) from h_2466)))))
          have h_2469 : (by
            let _equal_wd_1_0 := _object_h2548
            let _equal_wd_1_1 := (Litex.div (Litex.add _object_h2542 _object_h2545 (Litex.realToComplex _object_h2542 h_2542) (Litex.realToComplex _object_h2545 h_2545)) (Litex.number (M := M) (2 : ℂ)) (Litex.addInC _object_h2542 _object_h2545 (Litex.realToComplex _object_h2542 h_2542) (Litex.realToComplex _object_h2545 h_2545)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.numberNonzero (M := M) (2 : ℂ) (by norm_num)))
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  h_2553
                )
            )
          have h_2470 : (by
            let _equal_wd_1_0 := _object_h2549
            let _equal_wd_1_1 := (Litex.div (Litex.add _object_h2543 _object_h2546 (Litex.realToComplex _object_h2543 h_2543) (Litex.realToComplex _object_h2546 h_2546)) (Litex.number (M := M) (2 : ℂ)) (Litex.addInC _object_h2543 _object_h2546 (Litex.realToComplex _object_h2543 h_2543) (Litex.realToComplex _object_h2546 h_2546)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.numberNonzero (M := M) (2 : ℂ) (by norm_num)))
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  h_2554
                )
            )
          let _object_w102 := (let _litex_call_arg_0 := _value_i22;
          let _litex_call_arg_1 := _value_i24;
          Litex.callOn ((_object_i13 (M := M))).val.signature (_object_i13 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1820 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
            exact h_2541) (by
            let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
            exact h_2547)), True.intro⟩))

          let _object_w103 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := _object_h2548;
          let _wd_3_1 := _object_h2542;
          (Litex.sub _wd_3_0 _wd_3_1 (by
            let _atomic_wd_1_0 := _wd_3_0
            exact (M.real_subset_complex _ h_2548)) (by
            let _atomic_wd_1_0 := _wd_3_1
            exact (M.real_subset_complex _ h_2542))));
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.subInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right h_2548 h_2542)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          let _wd_1_1 := (let _wd_2_0 := (let _wd_3_0 := _object_h2549;
          let _wd_3_1 := _object_h2543;
          (Litex.sub _wd_3_0 _wd_3_1 (by
            let _atomic_wd_1_0 := _wd_3_0
            exact (M.real_subset_complex _ h_2549)) (by
            let _atomic_wd_1_0 := _wd_3_1
            exact (M.real_subset_complex _ h_2543))));
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.subInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right h_2549 h_2543)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.subInC ((_atomic_wd_1_0).val.base).val.left ((_atomic_wd_1_0).val.base).val.right (M.real_subset_complex _ h_2548) (M.real_subset_complex _ h_2542))
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            )) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.subInC ((_atomic_wd_1_0).val.base).val.left ((_atomic_wd_1_0).val.base).val.right (M.real_subset_complex _ h_2549) (M.real_subset_complex _ h_2543))
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            ))))

          have h_2471 : (by
            let _equal_wd_1_0 := _object_w102
            let _equal_wd_1_1 := _object_w103
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w102;
                  let _equal_wd_1_1 := _object_w103;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i13 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i22), (Litex.denote _value_i24)])) = (M.addValue (M.powValue (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))) (M.number (2 : ℂ))) (M.powValue (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ)))) (M.number (2 : ℂ)))) from by
                    have _litex_residual : (M.addValue (M.mulValue (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ))))) (M.mulValue (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ)))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ)))))) = (M.addValue (M.powValue (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))) (M.number (2 : ℂ))) (M.powValue (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ)))) (M.number (2 : ℂ)))) := (let _equal_wd_2_0 := (let _wd_1_0 := (let _wd_2_0 := ((_equal_wd_1_1).val.left).val.base;
                    let _wd_2_1 := _wd_2_0;
                    (Litex.mul _wd_2_0 _wd_2_1 (by
                      let _atomic_wd_1_0 := _wd_2_1
                      exact (Litex.subInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (M.real_subset_complex _ h_2548) (M.real_subset_complex _ h_2542))) (by
                      let _atomic_wd_1_0 := _wd_2_1
                      exact (Litex.subInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (M.real_subset_complex _ h_2548) (M.real_subset_complex _ h_2542)))));
                    let _wd_1_1 := (let _wd_2_0 := ((_equal_wd_1_1).val.right).val.base;
                    let _wd_2_1 := _wd_2_0;
                    (Litex.mul _wd_2_0 _wd_2_1 (by
                      let _atomic_wd_1_0 := _wd_2_1
                      exact (Litex.subInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (M.real_subset_complex _ h_2549) (M.real_subset_complex _ h_2543))) (by
                      let _atomic_wd_1_0 := _wd_2_1
                      exact (Litex.subInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (M.real_subset_complex _ h_2549) (M.real_subset_complex _ h_2543)))));
                    (Litex.add _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.mulInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.left (Litex.subInC ((_atomic_wd_1_0).val.left).val.left ((_atomic_wd_1_0).val.left).val.right (M.real_subset_complex _ h_2548) (M.real_subset_complex _ h_2542)) (Litex.subInC ((_atomic_wd_1_0).val.left).val.left ((_atomic_wd_1_0).val.left).val.right (M.real_subset_complex _ h_2548) (M.real_subset_complex _ h_2542)))) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (Litex.mulInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.left (Litex.subInC ((_atomic_wd_1_0).val.left).val.left ((_atomic_wd_1_0).val.left).val.right (M.real_subset_complex _ h_2549) (M.real_subset_complex _ h_2543)) (Litex.subInC ((_atomic_wd_1_0).val.left).val.left ((_atomic_wd_1_0).val.left).val.right (M.real_subset_complex _ h_2549) (M.real_subset_complex _ h_2543))))));
                    let _equal_wd_2_1 := _equal_wd_1_1;
                    (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((((Litex.NativeBridge.asComplex _object_h2548 (Litex.realToComplex _object_h2548 h_2548)) - (Litex.NativeBridge.asComplex _object_h2542 (Litex.realToComplex _object_h2542 h_2542))) * ((Litex.NativeBridge.asComplex _object_h2548 (Litex.realToComplex _object_h2548 h_2548)) - (Litex.NativeBridge.asComplex _object_h2542 (Litex.realToComplex _object_h2542 h_2542)))) + (((Litex.NativeBridge.asComplex _object_h2549 (Litex.realToComplex _object_h2549 h_2549)) - (Litex.NativeBridge.asComplex _object_h2543 (Litex.realToComplex _object_h2543 h_2543))) * ((Litex.NativeBridge.asComplex _object_h2549 (Litex.realToComplex _object_h2549 h_2549)) - (Litex.NativeBridge.asComplex _object_h2543 (Litex.realToComplex _object_h2543 h_2543))))) ((((Litex.NativeBridge.asComplex _object_h2548 (Litex.realToComplex _object_h2548 h_2548)) - (Litex.NativeBridge.asComplex _object_h2542 (Litex.realToComplex _object_h2542 h_2542))) ^ (2 : ℕ)) + (((Litex.NativeBridge.asComplex _object_h2549 (Litex.realToComplex _object_h2549 h_2549)) - (Litex.NativeBridge.asComplex _object_h2543 (Litex.realToComplex _object_h2543 h_2543))) ^ (2 : ℕ))) (Litex.NativeBridge.denoteAdd (_equal_wd_2_0).val.left (_equal_wd_2_0).val.right (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteMul ((_equal_wd_2_0).val.left).val.left ((_equal_wd_2_0).val.left).val.right ((_equal_wd_2_0).val.left).wd.1 ((_equal_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteSub (((_equal_wd_2_0).val.left).val.left).val.left (((_equal_wd_2_0).val.left).val.left).val.right (((_equal_wd_2_0).val.left).val.left).wd.1 (((_equal_wd_2_0).val.left).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _object_h2548 (Litex.realToComplex _object_h2548 h_2548)) (Litex.NativeBridge.asComplex_spec _object_h2542 (Litex.realToComplex _object_h2542 h_2542))) (Litex.NativeBridge.denoteSub (((_equal_wd_2_0).val.left).val.right).val.left (((_equal_wd_2_0).val.left).val.right).val.right (((_equal_wd_2_0).val.left).val.right).wd.1 (((_equal_wd_2_0).val.left).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _object_h2548 (Litex.realToComplex _object_h2548 h_2548)) (Litex.NativeBridge.asComplex_spec _object_h2542 (Litex.realToComplex _object_h2542 h_2542)))) (Litex.NativeBridge.denoteMul ((_equal_wd_2_0).val.right).val.left ((_equal_wd_2_0).val.right).val.right ((_equal_wd_2_0).val.right).wd.1 ((_equal_wd_2_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteSub (((_equal_wd_2_0).val.right).val.left).val.left (((_equal_wd_2_0).val.right).val.left).val.right (((_equal_wd_2_0).val.right).val.left).wd.1 (((_equal_wd_2_0).val.right).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _object_h2549 (Litex.realToComplex _object_h2549 h_2549)) (Litex.NativeBridge.asComplex_spec _object_h2543 (Litex.realToComplex _object_h2543 h_2543))) (Litex.NativeBridge.denoteSub (((_equal_wd_2_0).val.right).val.right).val.left (((_equal_wd_2_0).val.right).val.right).val.right (((_equal_wd_2_0).val.right).val.right).wd.1 (((_equal_wd_2_0).val.right).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _object_h2549 (Litex.realToComplex _object_h2549 h_2549)) (Litex.NativeBridge.asComplex_spec _object_h2543 (Litex.realToComplex _object_h2543 h_2543))))) (Litex.NativeBridge.denoteAdd (_equal_wd_2_1).val.left (_equal_wd_2_1).val.right (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal ((_equal_wd_2_1).val.left).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                      let _atomic_wd_1_0 := ((_equal_wd_2_1).val.left).val.base
                      exact (Litex.subInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right h_2548 h_2542)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteSub (((_equal_wd_2_1).val.left).val.base).val.left (((_equal_wd_2_1).val.left).val.base).val.right (((_equal_wd_2_1).val.left).val.base).wd.1 (((_equal_wd_2_1).val.left).val.base).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _object_h2548 (Litex.realToComplex _object_h2548 h_2548)) (Litex.NativeBridge.asComplex_spec _object_h2542 (Litex.realToComplex _object_h2542 h_2542)))) (Litex.NativeBridge.denotePowNatReal ((_equal_wd_2_1).val.right).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                      let _atomic_wd_1_0 := ((_equal_wd_2_1).val.right).val.base
                      exact (Litex.subInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right h_2549 h_2543)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteSub (((_equal_wd_2_1).val.right).val.base).val.left (((_equal_wd_2_1).val.right).val.base).val.right (((_equal_wd_2_1).val.right).val.base).wd.1 (((_equal_wd_2_1).val.right).val.base).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _object_h2549 (Litex.realToComplex _object_h2549 h_2549)) (Litex.NativeBridge.asComplex_spec _object_h2543 (Litex.realToComplex _object_h2543 h_2543))))) (by ring!))))
                    exact ((((((((((((((((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i13 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i22), (Litex.denote _value_i24)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i13 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i22), (Litex.denote _value_i24)])) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i22), (Litex.denote _value_i24)])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i22), (Litex.denote _value_i24)]))])) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i13 (M := M));
                  let _wd_1_1 := _value_i22;
                  let _wd_1_2 := _value_i24;
                  (let _litex_call_arg_0 := _wd_1_1;
                  let _litex_call_arg_1 := _wd_1_2;
                  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
                    have _finiteProof_1 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _wd_1_0 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.formulaFnInFnSet _wd_1_0) (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2541) (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2547)) True.intro))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_1821 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i14, _raw_i15])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i14, _raw_i15]))]))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i22), (Litex.denote _value_i24)])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i22), (Litex.denote _value_i24)]))])); exact (congrArg₂ (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i14, _raw_i15])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i14, _raw_i15]))]))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i22), (Litex.denote _value_i24)]) (M.number (1 : ℂ)) = (Litex.denote _value_i22) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i22), (Litex.denote _value_i24)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i22), (Litex.denote _value_i24)]) (M.number (2 : ℂ)) = (Litex.denote _value_i24) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i22), (Litex.denote _value_i24)] (1 : Fin 2)))))
                  ))).trans (congrArg (fun _x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_x, (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i22), (Litex.denote _value_i24)]))])) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i22), (Litex.denote _value_i24)])) = (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))]) from by
                    let _litex_original := (let _litex_call_arg_0 := _value_i22;
                  let _litex_call_arg_1 := _value_i24;
                  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_611 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2541) (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2547)), True.intro⟩))
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                  let _wd_1_1 := _value_i22;
                  let _wd_1_2 := _value_i24;
                  (let _litex_call_arg_0 := _wd_1_1;
                  let _litex_call_arg_1 := _wd_1_2;
                  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
                    have _finiteProof_1 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _wd_1_0 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.formulaFnInFnSet _wd_1_0) (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2541) (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2547)) True.intro))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_612 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) _raw_i3 (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i2 (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) _raw_i3 (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i2 (M.number (2 : ℂ))))])) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))]); exact (congrArg₂ (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) _raw_i3 (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i2 (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) _raw_i3 (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i2 (M.number (2 : ℂ))))])) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i22), (Litex.denote _value_i24)]) (M.number (1 : ℂ)) = (Litex.denote _value_i22) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i22), (Litex.denote _value_i24)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i22), (Litex.denote _value_i24)]) (M.number (2 : ℂ)) = (Litex.denote _value_i24) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i22), (Litex.denote _value_i24)] (1 : Fin 2)))))
                  )))).trans (congrArg (fun _x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))]), _x])) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i22), (Litex.denote _value_i24)])) = (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))]) from by
                    let _litex_original := (let _litex_call_arg_0 := _value_i22;
                  let _litex_call_arg_1 := _value_i24;
                  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_611 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2541) (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2547)), True.intro⟩))
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                  let _wd_1_1 := _value_i22;
                  let _wd_1_2 := _value_i24;
                  (let _litex_call_arg_0 := _wd_1_1;
                  let _litex_call_arg_1 := _wd_1_2;
                  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
                    have _finiteProof_1 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _wd_1_0 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.formulaFnInFnSet _wd_1_0) (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2541) (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2547)) True.intro))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_612 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) _raw_i3 (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i2 (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) _raw_i3 (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i2 (M.number (2 : ℂ))))])) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))]); exact (congrArg₂ (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) _raw_i3 (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i2 (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) _raw_i3 (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i2 (M.number (2 : ℂ))))])) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i22), (Litex.denote _value_i24)]) (M.number (1 : ℂ)) = (Litex.denote _value_i22) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i22), (Litex.denote _value_i24)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i22), (Litex.denote _value_i24)]) (M.number (2 : ℂ)) = (Litex.denote _value_i24) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i22), (Litex.denote _value_i24)] (1 : Fin 2)))))
                  )))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))]), (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))])])) = (M.addValue (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))]) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))]) (M.number (1 : ℂ)))) (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))]) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))]) (M.number (2 : ℂ))))) from by
                    let _litex_original := (let _object_w80 := (let _wd_2_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_2_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_2_0;
                  let _productChild_1 := _wd_2_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )));
                  let _wd_1_1 := _object_w80;
                  (let _litex_call_arg_0 := _object_w80;
                  let _litex_call_arg_1 := _wd_1_1;
                  Litex.callOn ((_object_i8 (M := M))).val.signature (_object_i8 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1453 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                    let _atomic_wd_1_0 := _object_w80
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact (by
                      let _checked_domain_target := (by
                      have _checked_header : ∀ (_raw_i26 : M.Value), M.mem _raw_i26 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) → ((fun (_raw_i26 : M.Value) => True) _raw_i26) → True := by
                        intro _raw_i26 h_5482 _
                        let _value_i26 := Litex.semanticObject (M := M) _raw_i26 (M.member_isSet h_5482)
                        have h_5482 : Litex.In _value_i26 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) := h_5482
                        exact True.intro
                      exact Litex.fnSet (Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.denote (Litex.union (Litex.R (M := M)) (Litex.R (M := M)))) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.isSet (Litex.union (Litex.R (M := M)) (Litex.R (M := M)))) (fun (_litex_input : M.Value) => (fun (_raw_i26 : M.Value) => True) _litex_input)))
                      let _function := _object_w80
                      let _tuple := _atomic_wd_1_0
                      let _cart := _atomic_wd_1_1
                      let _target := _atomic_wd_1_1
                      have _tupleMember : Litex.In _tuple _cart := Litex.tupleInCart _tuple _cart (by
                        have _finiteProof_0 := ((by
                          let _atomic_wd_2_0 := ((_equal_wd_1_1).val.left).val.base
                          exact (Litex.subInR (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right h_2548 h_2542)))
                        have _finiteProof_1 := ((by
                          let _atomic_wd_2_0 := ((_equal_wd_1_1).val.right).val.base
                          exact (Litex.subInR (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right h_2549 h_2543)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )
                      have _tupleSame : Litex.Same _function _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                      have _carrierSame : Litex.Same _target _cart := (show @Eq M.Value _ _ from Eq.refl _)
                      exact Litex.inOfSame _tuple _function _cart _target _tupleSame.symm _carrierSame.symm _tupleMember)) (by
                    let _atomic_wd_1_0 := _object_w80
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact (by
                      let _checked_domain_target := (by
                      have _checked_header : ∀ (_raw_i28 : M.Value), M.mem _raw_i28 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) → ((fun (_raw_i28 : M.Value) => True) _raw_i28) → True := by
                        intro _raw_i28 h_5992 _
                        let _value_i28 := Litex.semanticObject (M := M) _raw_i28 (M.member_isSet h_5992)
                        have h_5992 : Litex.In _value_i28 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) := h_5992
                        exact True.intro
                      exact Litex.fnSet (Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.denote (Litex.union (Litex.R (M := M)) (Litex.R (M := M)))) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.isSet (Litex.union (Litex.R (M := M)) (Litex.R (M := M)))) (fun (_litex_input : M.Value) => (fun (_raw_i28 : M.Value) => True) _litex_input)))
                      let _function := _object_w80
                      let _tuple := _atomic_wd_1_0
                      let _cart := _atomic_wd_1_1
                      let _target := _atomic_wd_1_1
                      have _tupleMember : Litex.In _tuple _cart := Litex.tupleInCart _tuple _cart (by
                        have _finiteProof_0 := ((by
                          let _atomic_wd_2_0 := ((_equal_wd_1_1).val.left).val.base
                          exact (Litex.subInR (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right h_2548 h_2542)))
                        have _finiteProof_1 := ((by
                          let _atomic_wd_2_0 := ((_equal_wd_1_1).val.right).val.base
                          exact (Litex.subInR (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right h_2549 h_2543)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )
                      have _tupleSame : Litex.Same _function _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                      have _carrierSame : Litex.Same _target _cart := (show @Eq M.Value _ _ from Eq.refl _)
                      exact Litex.inOfSame _tuple _function _cart _target _tupleSame.symm _carrierSame.symm _tupleMember))), True.intro⟩)))
                    let _litex_literal := (let _wd_1_0 := (_object_i8 (M := M));
                  let _object_w91 := (let _wd_2_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_2_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_2_0;
                  let _productChild_1 := _wd_2_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )));
                  let _wd_1_2 := _object_w91;
                  (let _litex_call_arg_0 := _object_w91;
                  let _litex_call_arg_1 := _wd_1_2;
                  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
                    have _finiteProof_1 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _wd_1_0 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.formulaFnInFnSet _wd_1_0) (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                    let _atomic_wd_1_0 := _object_w91
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact (by
                      let _checked_domain_target := (by
                      have _checked_header : ∀ (_raw_i30 : M.Value), M.mem _raw_i30 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) → ((fun (_raw_i30 : M.Value) => True) _raw_i30) → True := by
                        intro _raw_i30 h_6728 _
                        let _value_i30 := Litex.semanticObject (M := M) _raw_i30 (M.member_isSet h_6728)
                        have h_6728 : Litex.In _value_i30 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) := h_6728
                        exact True.intro
                      exact Litex.fnSet (Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.denote (Litex.union (Litex.R (M := M)) (Litex.R (M := M)))) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.isSet (Litex.union (Litex.R (M := M)) (Litex.R (M := M)))) (fun (_litex_input : M.Value) => (fun (_raw_i30 : M.Value) => True) _litex_input)))
                      let _function := _object_w91
                      let _tuple := _atomic_wd_1_0
                      let _cart := _atomic_wd_1_1
                      let _target := _atomic_wd_1_1
                      have _tupleMember : Litex.In _tuple _cart := Litex.tupleInCart _tuple _cart (by
                        have _finiteProof_0 := ((by
                          let _atomic_wd_2_0 := ((_equal_wd_1_1).val.left).val.base
                          exact (Litex.subInR (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right h_2548 h_2542)))
                        have _finiteProof_1 := ((by
                          let _atomic_wd_2_0 := ((_equal_wd_1_1).val.right).val.base
                          exact (Litex.subInR (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right h_2549 h_2543)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )
                      have _tupleSame : Litex.Same _function _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                      have _carrierSame : Litex.Same _target _cart := (show @Eq M.Value _ _ from Eq.refl _)
                      exact Litex.inOfSame _tuple _function _cart _target _tupleSame.symm _carrierSame.symm _tupleMember)) (by
                    let _atomic_wd_1_0 := _object_w91
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact (by
                      let _checked_domain_target := (by
                      have _checked_header : ∀ (_raw_i32 : M.Value), M.mem _raw_i32 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) → ((fun (_raw_i32 : M.Value) => True) _raw_i32) → True := by
                        intro _raw_i32 h_7238 _
                        let _value_i32 := Litex.semanticObject (M := M) _raw_i32 (M.member_isSet h_7238)
                        have h_7238 : Litex.In _value_i32 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) := h_7238
                        exact True.intro
                      exact Litex.fnSet (Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.denote (Litex.union (Litex.R (M := M)) (Litex.R (M := M)))) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.isSet (Litex.union (Litex.R (M := M)) (Litex.R (M := M)))) (fun (_litex_input : M.Value) => (fun (_raw_i32 : M.Value) => True) _litex_input)))
                      let _function := _object_w91
                      let _tuple := _atomic_wd_1_0
                      let _cart := _atomic_wd_1_1
                      let _target := _atomic_wd_1_1
                      have _tupleMember : Litex.In _tuple _cart := Litex.tupleInCart _tuple _cart (by
                        have _finiteProof_0 := ((by
                          let _atomic_wd_2_0 := ((_equal_wd_1_1).val.left).val.base
                          exact (Litex.subInR (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right h_2548 h_2542)))
                        have _finiteProof_1 := ((by
                          let _atomic_wd_2_0 := ((_equal_wd_1_1).val.right).val.base
                          exact (Litex.subInR (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right h_2549 h_2543)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )
                      have _tupleSame : Litex.Same _function _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                      have _carrierSame : Litex.Same _target _cart := (show @Eq M.Value _ _ from Eq.refl _)
                      exact Litex.inOfSame _tuple _function _cart _target _tupleSame.symm _carrierSame.symm _tupleMember))) True.intro))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_1454 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (M.addValue (M.mulValue (Litex.FunctionSemantics.callValue (M := M) _raw_i9 (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i10 (M.number (1 : ℂ)))) (M.mulValue (Litex.FunctionSemantics.callValue (M := M) _raw_i9 (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i10 (M.number (2 : ℂ)))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))]) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))]) (M.number (1 : ℂ)))) (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))]) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))]) (M.number (2 : ℂ))))); exact (congrArg₂ (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (M.addValue (M.mulValue (Litex.FunctionSemantics.callValue (M := M) _raw_i9 (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i10 (M.number (1 : ℂ)))) (M.mulValue (Litex.FunctionSemantics.callValue (M := M) _raw_i9 (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i10 (M.number (2 : ℂ)))))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))]), (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))])]) (M.number (1 : ℂ)) = (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))]) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))]), (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))])] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))]), (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))])]) (M.number (2 : ℂ)) = (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))]) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))]), (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))])] (1 : Fin 2)))))
                  ))).trans (congrArg₂ M.addValue (congrArg₂ M.mulValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))]) (M.number (1 : ℂ))) = (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))) from by
                    let _checked_call := (let _wd_1_0 := (let _wd_2_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_2_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_2_0;
                  let _productChild_1 := _wd_2_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )));
                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                  (let _receiver := _wd_1_0;
                  let _argument := _wd_1_1;
                  let _cart := (Litex.tupleSingletonCart _wd_1_0);
                  Litex.cartCall _receiver _cart _argument (by
                    let _tuple := _wd_1_0
                    let _receiver := _wd_1_0
                    have _same : Litex.Same _receiver _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                    exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
                    (Litex.indexSetMemberOfClosedRange (p := _argument) (n := 2) (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
                    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))))))
                    let _tuple := (let _wd_1_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_1_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_1_0;
                  let _productChild_1 := _wd_1_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )))
                    have _receiver : Litex.Same (let _wd_1_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_1_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_1_0;
                  let _productChild_1 := _wd_1_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  ))) _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                    have _coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _tuple) (M.number (1 : ℂ)) = _tuple.val.values (0 : Fin 2) := by
                      simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _tuple (0 : Fin 2))
                    have _component : _tuple.val.values (0 : Fin 2) = (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))) := rfl
                    exact (congrArg (fun value => Litex.FunctionSemantics.callValue (M := M) value (M.number (1 : ℂ))) _receiver).trans (_coordinate.trans _component)
                  ) rfl) rfl))).trans (congrArg₂ M.addValue (congrArg₂ M.mulValue rfl (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))]) (M.number (1 : ℂ))) = (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))) from by
                    let _checked_call := (let _wd_1_0 := (let _wd_2_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_2_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_2_0;
                  let _productChild_1 := _wd_2_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )));
                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                  (let _receiver := _wd_1_0;
                  let _argument := _wd_1_1;
                  let _cart := (Litex.tupleSingletonCart _wd_1_0);
                  Litex.cartCall _receiver _cart _argument (by
                    let _tuple := _wd_1_0
                    let _receiver := _wd_1_0
                    have _same : Litex.Same _receiver _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                    exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
                    (Litex.indexSetMemberOfClosedRange (p := _argument) (n := 2) (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
                    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))))))
                    let _tuple := (let _wd_1_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_1_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_1_0;
                  let _productChild_1 := _wd_1_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )))
                    have _receiver : Litex.Same (let _wd_1_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_1_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_1_0;
                  let _productChild_1 := _wd_1_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  ))) _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                    have _coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _tuple) (M.number (1 : ℂ)) = _tuple.val.values (0 : Fin 2) := by
                      simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _tuple (0 : Fin 2))
                    have _component : _tuple.val.values (0 : Fin 2) = (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))) := rfl
                    exact (congrArg (fun value => Litex.FunctionSemantics.callValue (M := M) value (M.number (1 : ℂ))) _receiver).trans (_coordinate.trans _component)
                  )) rfl))).trans (congrArg₂ M.addValue rfl (congrArg₂ M.mulValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))]) (M.number (2 : ℂ))) = (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ)))) from by
                    let _checked_call := (let _wd_1_0 := (let _wd_2_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_2_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_2_0;
                  let _productChild_1 := _wd_2_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )));
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (let _receiver := _wd_1_0;
                  let _argument := _wd_1_1;
                  let _cart := (Litex.tupleSingletonCart _wd_1_0);
                  Litex.cartCall _receiver _cart _argument (by
                    let _tuple := _wd_1_0
                    let _receiver := _wd_1_0
                    have _same : Litex.Same _receiver _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                    exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
                    (Litex.indexSetMemberOfClosedRange (p := _argument) (n := 2) (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
                    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))))))
                    let _tuple := (let _wd_1_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_1_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_1_0;
                  let _productChild_1 := _wd_1_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )))
                    have _receiver : Litex.Same (let _wd_1_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_1_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_1_0;
                  let _productChild_1 := _wd_1_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  ))) _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                    have _coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _tuple) (M.number (2 : ℂ)) = _tuple.val.values (1 : Fin 2) := by
                      simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _tuple (1 : Fin 2))
                    have _component : _tuple.val.values (1 : Fin 2) = (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ)))) := rfl
                    exact (congrArg (fun value => Litex.FunctionSemantics.callValue (M := M) value (M.number (2 : ℂ))) _receiver).trans (_coordinate.trans _component)
                  ) rfl)))).trans (congrArg₂ M.addValue rfl (congrArg₂ M.mulValue rfl (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))))]) (M.number (2 : ℂ))) = (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ)))) from by
                    let _checked_call := (let _wd_1_0 := (let _wd_2_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_2_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_2_0;
                  let _productChild_1 := _wd_2_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )));
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (let _receiver := _wd_1_0;
                  let _argument := _wd_1_1;
                  let _cart := (Litex.tupleSingletonCart _wd_1_0);
                  Litex.cartCall _receiver _cart _argument (by
                    let _tuple := _wd_1_0
                    let _receiver := _wd_1_0
                    have _same : Litex.Same _receiver _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                    exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
                    (Litex.indexSetMemberOfClosedRange (p := _argument) (n := 2) (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
                    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))))))
                    let _tuple := (let _wd_1_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_1_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_1_0;
                  let _productChild_1 := _wd_1_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )))
                    have _receiver : Litex.Same (let _wd_1_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_1_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_1_0;
                  let _productChild_1 := _wd_1_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  ))) _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                    have _coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _tuple) (M.number (2 : ℂ)) = _tuple.val.values (1 : Fin 2) := by
                      simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _tuple (1 : Fin 2))
                    have _component : _tuple.val.values (1 : Fin 2) = (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ)))) := rfl
                    exact (congrArg (fun value => Litex.FunctionSemantics.callValue (M := M) value (M.number (2 : ℂ))) _receiver).trans (_coordinate.trans _component)
                  ))))).trans _litex_residual)))
                )
            )
          let _object_w126 := (let _litex_call_arg_0 := _value_i23;
          let _litex_call_arg_1 := _value_i24;
          Litex.callOn ((_object_i13 (M := M))).val.signature (_object_i13 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1820 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
            exact h_2544) (by
            let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
            exact h_2547)), True.intro⟩))

          let _object_w127 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (((_object_w103).val.left).val.base).val.left;
          let _wd_3_1 := _object_h2545;
          (Litex.sub _wd_3_0 _wd_3_1 (by
            let _atomic_wd_1_0 := _wd_3_0
            exact (M.real_subset_complex _ h_2548)) (by
            let _atomic_wd_1_0 := _wd_3_1
            exact (M.real_subset_complex _ h_2545))));
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.subInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right h_2548 h_2545)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          let _wd_1_1 := (let _wd_2_0 := (let _wd_3_0 := (((_object_w103).val.right).val.base).val.left;
          let _wd_3_1 := _object_h2546;
          (Litex.sub _wd_3_0 _wd_3_1 (by
            let _atomic_wd_1_0 := _wd_3_0
            exact (M.real_subset_complex _ h_2549)) (by
            let _atomic_wd_1_0 := _wd_3_1
            exact (M.real_subset_complex _ h_2546))));
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.subInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right h_2549 h_2546)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.subInC ((_atomic_wd_1_0).val.base).val.left ((_atomic_wd_1_0).val.base).val.right (M.real_subset_complex _ h_2548) (M.real_subset_complex _ h_2545))
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            )) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.subInC ((_atomic_wd_1_0).val.base).val.left ((_atomic_wd_1_0).val.base).val.right (M.real_subset_complex _ h_2549) (M.real_subset_complex _ h_2546))
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            ))))

          have h_2472 : (by
            let _equal_wd_1_0 := _object_w126
            let _equal_wd_1_1 := _object_w127
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w126;
                  let _equal_wd_1_1 := _object_w127;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i13 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i23), (Litex.denote _value_i24)])) = (M.addValue (M.powValue (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))) (M.number (2 : ℂ))) (M.powValue (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ)))) (M.number (2 : ℂ)))) from by
                    have _litex_residual : (M.addValue (M.mulValue (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ))))) (M.mulValue (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ)))) (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ)))))) = (M.addValue (M.powValue (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))) (M.number (2 : ℂ))) (M.powValue (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ)))) (M.number (2 : ℂ)))) := (let _equal_wd_2_0 := (let _wd_1_0 := (let _wd_2_0 := ((_equal_wd_1_1).val.left).val.base;
                    let _wd_2_1 := _wd_2_0;
                    (Litex.mul _wd_2_0 _wd_2_1 (by
                      let _atomic_wd_1_0 := _wd_2_1
                      exact (Litex.subInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (M.real_subset_complex _ h_2548) (M.real_subset_complex _ h_2545))) (by
                      let _atomic_wd_1_0 := _wd_2_1
                      exact (Litex.subInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (M.real_subset_complex _ h_2548) (M.real_subset_complex _ h_2545)))));
                    let _wd_1_1 := (let _wd_2_0 := ((_equal_wd_1_1).val.right).val.base;
                    let _wd_2_1 := _wd_2_0;
                    (Litex.mul _wd_2_0 _wd_2_1 (by
                      let _atomic_wd_1_0 := _wd_2_1
                      exact (Litex.subInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (M.real_subset_complex _ h_2549) (M.real_subset_complex _ h_2546))) (by
                      let _atomic_wd_1_0 := _wd_2_1
                      exact (Litex.subInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (M.real_subset_complex _ h_2549) (M.real_subset_complex _ h_2546)))));
                    (Litex.add _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := _wd_1_0
                      exact (Litex.mulInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.left (Litex.subInC ((_atomic_wd_1_0).val.left).val.left ((_atomic_wd_1_0).val.left).val.right (M.real_subset_complex _ h_2548) (M.real_subset_complex _ h_2545)) (Litex.subInC ((_atomic_wd_1_0).val.left).val.left ((_atomic_wd_1_0).val.left).val.right (M.real_subset_complex _ h_2548) (M.real_subset_complex _ h_2545)))) (by
                      let _atomic_wd_1_0 := _wd_1_1
                      exact (Litex.mulInC (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.left (Litex.subInC ((_atomic_wd_1_0).val.left).val.left ((_atomic_wd_1_0).val.left).val.right (M.real_subset_complex _ h_2549) (M.real_subset_complex _ h_2546)) (Litex.subInC ((_atomic_wd_1_0).val.left).val.left ((_atomic_wd_1_0).val.left).val.right (M.real_subset_complex _ h_2549) (M.real_subset_complex _ h_2546))))));
                    let _equal_wd_2_1 := _equal_wd_1_1;
                    (show Litex.Same _equal_wd_2_0 _equal_wd_2_1 from (Litex.NativeBridge.sameOfDenoteNumber _ _ ((((Litex.NativeBridge.asComplex _object_h2548 (Litex.realToComplex _object_h2548 h_2548)) - (Litex.NativeBridge.asComplex _object_h2545 (Litex.realToComplex _object_h2545 h_2545))) * ((Litex.NativeBridge.asComplex _object_h2548 (Litex.realToComplex _object_h2548 h_2548)) - (Litex.NativeBridge.asComplex _object_h2545 (Litex.realToComplex _object_h2545 h_2545)))) + (((Litex.NativeBridge.asComplex _object_h2549 (Litex.realToComplex _object_h2549 h_2549)) - (Litex.NativeBridge.asComplex _object_h2546 (Litex.realToComplex _object_h2546 h_2546))) * ((Litex.NativeBridge.asComplex _object_h2549 (Litex.realToComplex _object_h2549 h_2549)) - (Litex.NativeBridge.asComplex _object_h2546 (Litex.realToComplex _object_h2546 h_2546))))) ((((Litex.NativeBridge.asComplex _object_h2548 (Litex.realToComplex _object_h2548 h_2548)) - (Litex.NativeBridge.asComplex _object_h2545 (Litex.realToComplex _object_h2545 h_2545))) ^ (2 : ℕ)) + (((Litex.NativeBridge.asComplex _object_h2549 (Litex.realToComplex _object_h2549 h_2549)) - (Litex.NativeBridge.asComplex _object_h2546 (Litex.realToComplex _object_h2546 h_2546))) ^ (2 : ℕ))) (Litex.NativeBridge.denoteAdd (_equal_wd_2_0).val.left (_equal_wd_2_0).val.right (_equal_wd_2_0).wd.1 (_equal_wd_2_0).wd.2 _ _ (Litex.NativeBridge.denoteMul ((_equal_wd_2_0).val.left).val.left ((_equal_wd_2_0).val.left).val.right ((_equal_wd_2_0).val.left).wd.1 ((_equal_wd_2_0).val.left).wd.2 _ _ (Litex.NativeBridge.denoteSub (((_equal_wd_2_0).val.left).val.left).val.left (((_equal_wd_2_0).val.left).val.left).val.right (((_equal_wd_2_0).val.left).val.left).wd.1 (((_equal_wd_2_0).val.left).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _object_h2548 (Litex.realToComplex _object_h2548 h_2548)) (Litex.NativeBridge.asComplex_spec _object_h2545 (Litex.realToComplex _object_h2545 h_2545))) (Litex.NativeBridge.denoteSub (((_equal_wd_2_0).val.left).val.right).val.left (((_equal_wd_2_0).val.left).val.right).val.right (((_equal_wd_2_0).val.left).val.right).wd.1 (((_equal_wd_2_0).val.left).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _object_h2548 (Litex.realToComplex _object_h2548 h_2548)) (Litex.NativeBridge.asComplex_spec _object_h2545 (Litex.realToComplex _object_h2545 h_2545)))) (Litex.NativeBridge.denoteMul ((_equal_wd_2_0).val.right).val.left ((_equal_wd_2_0).val.right).val.right ((_equal_wd_2_0).val.right).wd.1 ((_equal_wd_2_0).val.right).wd.2 _ _ (Litex.NativeBridge.denoteSub (((_equal_wd_2_0).val.right).val.left).val.left (((_equal_wd_2_0).val.right).val.left).val.right (((_equal_wd_2_0).val.right).val.left).wd.1 (((_equal_wd_2_0).val.right).val.left).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _object_h2549 (Litex.realToComplex _object_h2549 h_2549)) (Litex.NativeBridge.asComplex_spec _object_h2546 (Litex.realToComplex _object_h2546 h_2546))) (Litex.NativeBridge.denoteSub (((_equal_wd_2_0).val.right).val.right).val.left (((_equal_wd_2_0).val.right).val.right).val.right (((_equal_wd_2_0).val.right).val.right).wd.1 (((_equal_wd_2_0).val.right).val.right).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _object_h2549 (Litex.realToComplex _object_h2549 h_2549)) (Litex.NativeBridge.asComplex_spec _object_h2546 (Litex.realToComplex _object_h2546 h_2546))))) (Litex.NativeBridge.denoteAdd (_equal_wd_2_1).val.left (_equal_wd_2_1).val.right (_equal_wd_2_1).wd.1 (_equal_wd_2_1).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal ((_equal_wd_2_1).val.left).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                      let _atomic_wd_1_0 := ((_equal_wd_2_1).val.left).val.base
                      exact (Litex.subInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right h_2548 h_2545)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteSub (((_equal_wd_2_1).val.left).val.base).val.left (((_equal_wd_2_1).val.left).val.base).val.right (((_equal_wd_2_1).val.left).val.base).wd.1 (((_equal_wd_2_1).val.left).val.base).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _object_h2548 (Litex.realToComplex _object_h2548 h_2548)) (Litex.NativeBridge.asComplex_spec _object_h2545 (Litex.realToComplex _object_h2545 h_2545)))) (Litex.NativeBridge.denotePowNatReal ((_equal_wd_2_1).val.right).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                      let _atomic_wd_1_0 := ((_equal_wd_2_1).val.right).val.base
                      exact (Litex.subInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right h_2549 h_2546)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteSub (((_equal_wd_2_1).val.right).val.base).val.left (((_equal_wd_2_1).val.right).val.base).val.right (((_equal_wd_2_1).val.right).val.base).wd.1 (((_equal_wd_2_1).val.right).val.base).wd.2 _ _ (Litex.NativeBridge.asComplex_spec _object_h2549 (Litex.realToComplex _object_h2549 h_2549)) (Litex.NativeBridge.asComplex_spec _object_h2546 (Litex.realToComplex _object_h2546 h_2546))))) (by ring!))))
                    exact ((((((((((((((((((Eq.refl (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i13 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i23), (Litex.denote _value_i24)])))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i13 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i23), (Litex.denote _value_i24)])) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i23), (Litex.denote _value_i24)])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i23), (Litex.denote _value_i24)]))])) from by
                    let _litex_original := _equal_wd_1_0
                    let _litex_literal := (let _wd_1_0 := (_object_i13 (M := M));
                  let _wd_1_1 := _value_i23;
                  let _wd_1_2 := _value_i24;
                  (let _litex_call_arg_0 := _wd_1_1;
                  let _litex_call_arg_1 := _wd_1_2;
                  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
                    have _finiteProof_1 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _wd_1_0 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.formulaFnInFnSet _wd_1_0) (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2544) (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2547)) True.intro))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_1821 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i14, _raw_i15])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i14, _raw_i15]))]))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i23), (Litex.denote _value_i24)])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i23), (Litex.denote _value_i24)]))])); exact (congrArg₂ (fun (_raw_i14 : M.Value) (_raw_i15 : M.Value) => (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i14, _raw_i15])), (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_raw_i14, _raw_i15]))]))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i23), (Litex.denote _value_i24)]) (M.number (1 : ℂ)) = (Litex.denote _value_i23) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i23), (Litex.denote _value_i24)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i23), (Litex.denote _value_i24)]) (M.number (2 : ℂ)) = (Litex.denote _value_i24) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i23), (Litex.denote _value_i24)] (1 : Fin 2)))))
                  ))).trans (congrArg (fun _x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![_x, (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i23), (Litex.denote _value_i24)]))])) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i23), (Litex.denote _value_i24)])) = (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))]) from by
                    let _litex_original := (let _litex_call_arg_0 := _value_i23;
                  let _litex_call_arg_1 := _value_i24;
                  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_611 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2544) (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2547)), True.intro⟩))
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                  let _wd_1_1 := _value_i23;
                  let _wd_1_2 := _value_i24;
                  (let _litex_call_arg_0 := _wd_1_1;
                  let _litex_call_arg_1 := _wd_1_2;
                  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
                    have _finiteProof_1 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _wd_1_0 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.formulaFnInFnSet _wd_1_0) (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2544) (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2547)) True.intro))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_612 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) _raw_i3 (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i2 (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) _raw_i3 (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i2 (M.number (2 : ℂ))))])) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))]); exact (congrArg₂ (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) _raw_i3 (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i2 (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) _raw_i3 (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i2 (M.number (2 : ℂ))))])) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i23), (Litex.denote _value_i24)]) (M.number (1 : ℂ)) = (Litex.denote _value_i23) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i23), (Litex.denote _value_i24)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i23), (Litex.denote _value_i24)]) (M.number (2 : ℂ)) = (Litex.denote _value_i24) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i23), (Litex.denote _value_i24)] (1 : Fin 2)))))
                  )))).trans (congrArg (fun _x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))]), _x])) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i1 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.denote _value_i23), (Litex.denote _value_i24)])) = (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))]) from by
                    let _litex_original := (let _litex_call_arg_0 := _value_i23;
                  let _litex_call_arg_1 := _value_i24;
                  Litex.callOn ((_object_i1 (M := M))).val.signature (_object_i1 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_611 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2544) (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2547)), True.intro⟩))
                    let _litex_literal := (let _wd_1_0 := (_object_i1 (M := M));
                  let _wd_1_1 := _value_i23;
                  let _wd_1_2 := _value_i24;
                  (let _litex_call_arg_0 := _wd_1_1;
                  let _litex_call_arg_1 := _wd_1_2;
                  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
                    have _finiteProof_1 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _wd_1_0 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.formulaFnInFnSet _wd_1_0) (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2544) (by
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact h_2547)) True.intro))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_612 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) _raw_i3 (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i2 (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) _raw_i3 (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i2 (M.number (2 : ℂ))))])) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))]); exact (congrArg₂ (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) _raw_i3 (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i2 (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) _raw_i3 (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i2 (M.number (2 : ℂ))))])) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i23), (Litex.denote _value_i24)]) (M.number (1 : ℂ)) = (Litex.denote _value_i23) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i23), (Litex.denote _value_i24)] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.denote _value_i23), (Litex.denote _value_i24)]) (M.number (2 : ℂ)) = (Litex.denote _value_i24) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.denote _value_i23), (Litex.denote _value_i24)] (1 : Fin 2)))))
                  )))).trans (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote (_object_i8 (M := M))) (Litex.FiniteFunction.tupleValue (M := M) ![(Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))]), (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))])])) = (M.addValue (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))]) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))]) (M.number (1 : ℂ)))) (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))]) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))]) (M.number (2 : ℂ))))) from by
                    let _litex_original := (let _object_w104 := (let _wd_2_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_2_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_2_0;
                  let _productChild_1 := _wd_2_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )));
                  let _wd_1_1 := _object_w104;
                  (let _litex_call_arg_0 := _object_w104;
                  let _litex_call_arg_1 := _wd_1_1;
                  Litex.callOn ((_object_i8 (M := M))).val.signature (_object_i8 (M := M)) (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (h_1453 (M := M)) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                    let _atomic_wd_1_0 := _object_w104
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact (by
                      let _checked_domain_target := (by
                      have _checked_header : ∀ (_raw_i62 : M.Value), M.mem _raw_i62 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) → ((fun (_raw_i62 : M.Value) => True) _raw_i62) → True := by
                        intro _raw_i62 h_17722 _
                        let _value_i62 := Litex.semanticObject (M := M) _raw_i62 (M.member_isSet h_17722)
                        have h_17722 : Litex.In _value_i62 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) := h_17722
                        exact True.intro
                      exact Litex.fnSet (Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.denote (Litex.union (Litex.R (M := M)) (Litex.R (M := M)))) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.isSet (Litex.union (Litex.R (M := M)) (Litex.R (M := M)))) (fun (_litex_input : M.Value) => (fun (_raw_i62 : M.Value) => True) _litex_input)))
                      let _function := _object_w104
                      let _tuple := _atomic_wd_1_0
                      let _cart := _atomic_wd_1_1
                      let _target := _atomic_wd_1_1
                      have _tupleMember : Litex.In _tuple _cart := Litex.tupleInCart _tuple _cart (by
                        have _finiteProof_0 := ((by
                          let _atomic_wd_2_0 := ((_equal_wd_1_1).val.left).val.base
                          exact (Litex.subInR (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right h_2548 h_2545)))
                        have _finiteProof_1 := ((by
                          let _atomic_wd_2_0 := ((_equal_wd_1_1).val.right).val.base
                          exact (Litex.subInR (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right h_2549 h_2546)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )
                      have _tupleSame : Litex.Same _function _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                      have _carrierSame : Litex.Same _target _cart := (show @Eq M.Value _ _ from Eq.refl _)
                      exact Litex.inOfSame _tuple _function _cart _target _tupleSame.symm _carrierSame.symm _tupleMember)) (by
                    let _atomic_wd_1_0 := _object_w104
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact (by
                      let _checked_domain_target := (by
                      have _checked_header : ∀ (_raw_i64 : M.Value), M.mem _raw_i64 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) → ((fun (_raw_i64 : M.Value) => True) _raw_i64) → True := by
                        intro _raw_i64 h_18244 _
                        let _value_i64 := Litex.semanticObject (M := M) _raw_i64 (M.member_isSet h_18244)
                        have h_18244 : Litex.In _value_i64 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) := h_18244
                        exact True.intro
                      exact Litex.fnSet (Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.denote (Litex.union (Litex.R (M := M)) (Litex.R (M := M)))) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.isSet (Litex.union (Litex.R (M := M)) (Litex.R (M := M)))) (fun (_litex_input : M.Value) => (fun (_raw_i64 : M.Value) => True) _litex_input)))
                      let _function := _object_w104
                      let _tuple := _atomic_wd_1_0
                      let _cart := _atomic_wd_1_1
                      let _target := _atomic_wd_1_1
                      have _tupleMember : Litex.In _tuple _cart := Litex.tupleInCart _tuple _cart (by
                        have _finiteProof_0 := ((by
                          let _atomic_wd_2_0 := ((_equal_wd_1_1).val.left).val.base
                          exact (Litex.subInR (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right h_2548 h_2545)))
                        have _finiteProof_1 := ((by
                          let _atomic_wd_2_0 := ((_equal_wd_1_1).val.right).val.base
                          exact (Litex.subInR (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right h_2549 h_2546)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )
                      have _tupleSame : Litex.Same _function _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                      have _carrierSame : Litex.Same _target _cart := (show @Eq M.Value _ _ from Eq.refl _)
                      exact Litex.inOfSame _tuple _function _cart _target _tupleSame.symm _carrierSame.symm _tupleMember))), True.intro⟩)))
                    let _litex_literal := (let _wd_1_0 := (_object_i8 (M := M));
                  let _object_w115 := (let _wd_2_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_2_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_2_0;
                  let _productChild_1 := _wd_2_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )));
                  let _wd_1_2 := _object_w115;
                  (let _litex_call_arg_0 := _object_w115;
                  let _litex_call_arg_1 := _wd_1_2;
                  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (Litex.denote (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
                    have _finiteProof_1 := (Litex.isSet (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _wd_1_0 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.formulaFnInFnSet _wd_1_0) (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
                    let _atomic_wd_1_0 := _object_w115
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact (by
                      let _checked_domain_target := (by
                      have _checked_header : ∀ (_raw_i66 : M.Value), M.mem _raw_i66 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) → ((fun (_raw_i66 : M.Value) => True) _raw_i66) → True := by
                        intro _raw_i66 h_18998 _
                        let _value_i66 := Litex.semanticObject (M := M) _raw_i66 (M.member_isSet h_18998)
                        have h_18998 : Litex.In _value_i66 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) := h_18998
                        exact True.intro
                      exact Litex.fnSet (Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.denote (Litex.union (Litex.R (M := M)) (Litex.R (M := M)))) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.isSet (Litex.union (Litex.R (M := M)) (Litex.R (M := M)))) (fun (_litex_input : M.Value) => (fun (_raw_i66 : M.Value) => True) _litex_input)))
                      let _function := _object_w115
                      let _tuple := _atomic_wd_1_0
                      let _cart := _atomic_wd_1_1
                      let _target := _atomic_wd_1_1
                      have _tupleMember : Litex.In _tuple _cart := Litex.tupleInCart _tuple _cart (by
                        have _finiteProof_0 := ((by
                          let _atomic_wd_2_0 := ((_equal_wd_1_1).val.left).val.base
                          exact (Litex.subInR (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right h_2548 h_2545)))
                        have _finiteProof_1 := ((by
                          let _atomic_wd_2_0 := ((_equal_wd_1_1).val.right).val.base
                          exact (Litex.subInR (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right h_2549 h_2546)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )
                      have _tupleSame : Litex.Same _function _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                      have _carrierSame : Litex.Same _target _cart := (show @Eq M.Value _ _ from Eq.refl _)
                      exact Litex.inOfSame _tuple _function _cart _target _tupleSame.symm _carrierSame.symm _tupleMember)) (by
                    let _atomic_wd_1_0 := _object_w115
                    let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                    exact (by
                      let _checked_domain_target := (by
                      have _checked_header : ∀ (_raw_i68 : M.Value), M.mem _raw_i68 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) → ((fun (_raw_i68 : M.Value) => True) _raw_i68) → True := by
                        intro _raw_i68 h_19520 _
                        let _value_i68 := Litex.semanticObject (M := M) _raw_i68 (M.member_isSet h_19520)
                        have h_19520 : Litex.In _value_i68 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) := h_19520
                        exact True.intro
                      exact Litex.fnSet (Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.denote (Litex.union (Litex.R (M := M)) (Litex.R (M := M)))) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.isSet (Litex.union (Litex.R (M := M)) (Litex.R (M := M)))) (fun (_litex_input : M.Value) => (fun (_raw_i68 : M.Value) => True) _litex_input)))
                      let _function := _object_w115
                      let _tuple := _atomic_wd_1_0
                      let _cart := _atomic_wd_1_1
                      let _target := _atomic_wd_1_1
                      have _tupleMember : Litex.In _tuple _cart := Litex.tupleInCart _tuple _cart (by
                        have _finiteProof_0 := ((by
                          let _atomic_wd_2_0 := ((_equal_wd_1_1).val.left).val.base
                          exact (Litex.subInR (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right h_2548 h_2545)))
                        have _finiteProof_1 := ((by
                          let _atomic_wd_2_0 := ((_equal_wd_1_1).val.right).val.base
                          exact (Litex.subInR (_atomic_wd_2_0).val.left (_atomic_wd_2_0).val.right h_2549 h_2546)))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )
                      have _tupleSame : Litex.Same _function _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                      have _carrierSame : Litex.Same _target _cart := (show @Eq M.Value _ _ from Eq.refl _)
                      exact Litex.inOfSame _tuple _function _cart _target _tupleSame.symm _carrierSame.symm _tupleMember))) True.intro))
                    have _litex_call_eq := Litex.callOnCongr _litex_original _litex_literal (h_1454 (M := M)) (Litex.sameRefl _litex_original.val.argument)
                    have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_literal.val.function.wd (Litex.denote _litex_literal.val.argument) _litex_literal.wd.2
                    exact _litex_call_eq.trans (_litex_beta.trans (by change (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (M.addValue (M.mulValue (Litex.FunctionSemantics.callValue (M := M) _raw_i9 (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i10 (M.number (1 : ℂ)))) (M.mulValue (Litex.FunctionSemantics.callValue (M := M) _raw_i9 (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i10 (M.number (2 : ℂ)))))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote _litex_literal.val.argument) = (M.addValue (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))]) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))]) (M.number (1 : ℂ)))) (M.mulValue (Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))]) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))]) (M.number (2 : ℂ))))); exact (congrArg₂ (fun (_raw_i9 : M.Value) (_raw_i10 : M.Value) => (M.addValue (M.mulValue (Litex.FunctionSemantics.callValue (M := M) _raw_i9 (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i10 (M.number (1 : ℂ)))) (M.mulValue (Litex.FunctionSemantics.callValue (M := M) _raw_i9 (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _raw_i10 (M.number (2 : ℂ)))))) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))]), (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))])]) (M.number (1 : ℂ)) = (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))]) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))]), (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))])] (0 : Fin 2)) (show Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue ![(Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))]), (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))])]) (M.number (2 : ℂ)) = (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))]) from by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.call_tuple ![(Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))]), (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))])] (1 : Fin 2)))))
                  ))).trans (congrArg₂ M.addValue (congrArg₂ M.mulValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))]) (M.number (1 : ℂ))) = (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))) from by
                    let _checked_call := (let _wd_1_0 := (let _wd_2_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_2_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_2_0;
                  let _productChild_1 := _wd_2_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )));
                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                  (let _receiver := _wd_1_0;
                  let _argument := _wd_1_1;
                  let _cart := (Litex.tupleSingletonCart _wd_1_0);
                  Litex.cartCall _receiver _cart _argument (by
                    let _tuple := _wd_1_0
                    let _receiver := _wd_1_0
                    have _same : Litex.Same _receiver _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                    exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
                    (Litex.indexSetMemberOfClosedRange (p := _argument) (n := 2) (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
                    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))))))
                    let _tuple := (let _wd_1_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_1_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_1_0;
                  let _productChild_1 := _wd_1_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )))
                    have _receiver : Litex.Same (let _wd_1_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_1_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_1_0;
                  let _productChild_1 := _wd_1_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  ))) _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                    have _coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _tuple) (M.number (1 : ℂ)) = _tuple.val.values (0 : Fin 2) := by
                      simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _tuple (0 : Fin 2))
                    have _component : _tuple.val.values (0 : Fin 2) = (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))) := rfl
                    exact (congrArg (fun value => Litex.FunctionSemantics.callValue (M := M) value (M.number (1 : ℂ))) _receiver).trans (_coordinate.trans _component)
                  ) rfl) rfl))).trans (congrArg₂ M.addValue (congrArg₂ M.mulValue rfl (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))]) (M.number (1 : ℂ))) = (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))) from by
                    let _checked_call := (let _wd_1_0 := (let _wd_2_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_2_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_2_0;
                  let _productChild_1 := _wd_2_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )));
                  let _wd_1_1 := (Litex.number (M := M) (1 : ℂ));
                  (let _receiver := _wd_1_0;
                  let _argument := _wd_1_1;
                  let _cart := (Litex.tupleSingletonCart _wd_1_0);
                  Litex.cartCall _receiver _cart _argument (by
                    let _tuple := _wd_1_0
                    let _receiver := _wd_1_0
                    have _same : Litex.Same _receiver _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                    exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
                    (Litex.indexSetMemberOfClosedRange (p := _argument) (n := 2) (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
                    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))))))
                    let _tuple := (let _wd_1_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_1_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_1_0;
                  let _productChild_1 := _wd_1_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )))
                    have _receiver : Litex.Same (let _wd_1_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_1_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_1_0;
                  let _productChild_1 := _wd_1_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  ))) _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                    have _coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _tuple) (M.number (1 : ℂ)) = _tuple.val.values (0 : Fin 2) := by
                      simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _tuple (0 : Fin 2))
                    have _component : _tuple.val.values (0 : Fin 2) = (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))) := rfl
                    exact (congrArg (fun value => Litex.FunctionSemantics.callValue (M := M) value (M.number (1 : ℂ))) _receiver).trans (_coordinate.trans _component)
                  )) rfl))).trans (congrArg₂ M.addValue rfl (congrArg₂ M.mulValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))]) (M.number (2 : ℂ))) = (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ)))) from by
                    let _checked_call := (let _wd_1_0 := (let _wd_2_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_2_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_2_0;
                  let _productChild_1 := _wd_2_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )));
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (let _receiver := _wd_1_0;
                  let _argument := _wd_1_1;
                  let _cart := (Litex.tupleSingletonCart _wd_1_0);
                  Litex.cartCall _receiver _cart _argument (by
                    let _tuple := _wd_1_0
                    let _receiver := _wd_1_0
                    have _same : Litex.Same _receiver _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                    exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
                    (Litex.indexSetMemberOfClosedRange (p := _argument) (n := 2) (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
                    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))))))
                    let _tuple := (let _wd_1_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_1_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_1_0;
                  let _productChild_1 := _wd_1_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )))
                    have _receiver : Litex.Same (let _wd_1_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_1_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_1_0;
                  let _productChild_1 := _wd_1_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  ))) _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                    have _coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _tuple) (M.number (2 : ℂ)) = _tuple.val.values (1 : Fin 2) := by
                      simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _tuple (1 : Fin 2))
                    have _component : _tuple.val.values (1 : Fin 2) = (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ)))) := rfl
                    exact (congrArg (fun value => Litex.FunctionSemantics.callValue (M := M) value (M.number (2 : ℂ))) _receiver).trans (_coordinate.trans _component)
                  ) rfl)))).trans (congrArg₂ M.addValue rfl (congrArg₂ M.mulValue rfl (show (Litex.FunctionSemantics.callValue (M := M) (Litex.FiniteFunction.tupleValue (M := M) ![(M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))), (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))))]) (M.number (2 : ℂ))) = (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ)))) from by
                    let _checked_call := (let _wd_1_0 := (let _wd_2_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_2_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_2_0;
                  let _productChild_1 := _wd_2_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )));
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (let _receiver := _wd_1_0;
                  let _argument := _wd_1_1;
                  let _cart := (Litex.tupleSingletonCart _wd_1_0);
                  Litex.cartCall _receiver _cart _argument (by
                    let _tuple := _wd_1_0
                    let _receiver := _wd_1_0
                    have _same : Litex.Same _receiver _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                    exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
                    (Litex.indexSetMemberOfClosedRange (p := _argument) (n := 2) (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
                    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))))))
                    let _tuple := (let _wd_1_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_1_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_1_0;
                  let _productChild_1 := _wd_1_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  )))
                    have _receiver : Litex.Same (let _wd_1_0 := ((_equal_wd_1_1).val.left).val.base;
                  let _wd_1_1 := ((_equal_wd_1_1).val.right).val.base;
                  (let _productChild_0 := _wd_1_0;
                  let _productChild_1 := _wd_1_1;
                  Litex.tuple (M := M) ![Litex.denote _productChild_0, Litex.denote _productChild_1] (by
                    have _finiteProof_0 := ((Litex.isSet _productChild_0))
                    have _finiteProof_1 := ((Litex.isSet _productChild_1))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  ))) _tuple := (show @Eq M.Value _ _ from Eq.refl _)
                    have _coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _tuple) (M.number (2 : ℂ)) = _tuple.val.values (1 : Fin 2) := by
                      simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _tuple (1 : Fin 2))
                    have _component : _tuple.val.values (1 : Fin 2) = (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ)))) := rfl
                    exact (congrArg (fun value => Litex.FunctionSemantics.callValue (M := M) value (M.number (2 : ℂ))) _receiver).trans (_coordinate.trans _component)
                  ))))).trans _litex_residual)))
                )
            )
          let _object_w128 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (Litex.div (Litex.add (((_object_w103).val.left).val.base).val.right (((_object_w127).val.left).val.base).val.right (Litex.realToComplex _object_h2542 h_2542) (Litex.realToComplex _object_h2545 h_2545)) (Litex.number (M := M) (2 : ℂ)) (Litex.addInC (((_object_w103).val.left).val.base).val.right (((_object_w127).val.left).val.base).val.right (Litex.realToComplex _object_h2542 h_2542) (Litex.realToComplex _object_h2545 h_2545)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.numberNonzero (M := M) (2 : ℂ) (by norm_num)));
          let _wd_3_1 := (((_object_w103).val.left).val.base).val.right;
          (Litex.sub _wd_3_0 _wd_3_1 (by
            let _atomic_wd_1_0 := _wd_3_0
            exact (M.real_subset_complex _ (Litex.inOfSame (((_object_w127).val.left).val.base).val.left _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) h_2553 (show @Eq M.Value _ _ from Eq.refl _) h_2548))) (by
            let _atomic_wd_1_0 := _wd_3_1
            exact (M.real_subset_complex _ h_2542))));
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.subInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.inOfSame (((_object_w127).val.left).val.base).val.left (_atomic_wd_1_0).val.left (Litex.R (M := M)) (Litex.R (M := M)) h_2553 (show @Eq M.Value _ _ from Eq.refl _) h_2548) h_2542)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          let _wd_1_1 := (let _wd_2_0 := (let _wd_3_0 := (Litex.div (Litex.add (((_object_w103).val.right).val.base).val.right (((_object_w127).val.right).val.base).val.right (Litex.realToComplex _object_h2543 h_2543) (Litex.realToComplex _object_h2546 h_2546)) (Litex.number (M := M) (2 : ℂ)) (Litex.addInC (((_object_w103).val.right).val.base).val.right (((_object_w127).val.right).val.base).val.right (Litex.realToComplex _object_h2543 h_2543) (Litex.realToComplex _object_h2546 h_2546)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.numberNonzero (M := M) (2 : ℂ) (by norm_num)));
          let _wd_3_1 := (((_object_w103).val.right).val.base).val.right;
          (Litex.sub _wd_3_0 _wd_3_1 (by
            let _atomic_wd_1_0 := _wd_3_0
            exact (M.real_subset_complex _ (Litex.inOfSame (((_object_w127).val.right).val.base).val.left _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) h_2554 (show @Eq M.Value _ _ from Eq.refl _) h_2549))) (by
            let _atomic_wd_1_0 := _wd_3_1
            exact (M.real_subset_complex _ h_2543))));
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.subInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.inOfSame (((_object_w127).val.right).val.base).val.left (_atomic_wd_1_0).val.left (Litex.R (M := M)) (Litex.R (M := M)) h_2554 (show @Eq M.Value _ _ from Eq.refl _) h_2549) h_2543)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.subInC ((_atomic_wd_1_0).val.base).val.left ((_atomic_wd_1_0).val.base).val.right (M.real_subset_complex _ (Litex.inOfSame (((_object_w127).val.left).val.base).val.left ((_atomic_wd_1_0).val.base).val.left (Litex.R (M := M)) (Litex.R (M := M)) h_2553 (show @Eq M.Value _ _ from Eq.refl _) h_2548)) (M.real_subset_complex _ h_2542))
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            )) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.subInC ((_atomic_wd_1_0).val.base).val.left ((_atomic_wd_1_0).val.base).val.right (M.real_subset_complex _ (Litex.inOfSame (((_object_w127).val.right).val.base).val.left ((_atomic_wd_1_0).val.base).val.left (Litex.R (M := M)) (Litex.R (M := M)) h_2554 (show @Eq M.Value _ _ from Eq.refl _) h_2549)) (M.real_subset_complex _ h_2543))
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            ))))

          have h_2473 : (by
            let _equal_wd_1_0 := _object_w103
            let _equal_wd_1_1 := _object_w128
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ M.addValue (show (M.powValue (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))) (M.number (2 : ℂ))) = (M.powValue (M.subValue (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))) (M.number (2 : ℂ))) from (congrArg₂ M.powValue (show (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))) = (M.subValue (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ)))) from (congrArg₂ M.subValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) = (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))) (M.number (2 : ℂ))) from h_2553) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ))) from (show @Eq M.Value _ _ from Eq.refl _)))) (show (M.number (2 : ℂ)) = (M.number (2 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)))) (show (M.powValue (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ)))) (M.number (2 : ℂ))) = (M.powValue (M.subValue (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ)))) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ)))) (M.number (2 : ℂ))) from (congrArg₂ M.powValue (show (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ)))) = (M.subValue (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ)))) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ)))) from (congrArg₂ M.subValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) = (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ)))) (M.number (2 : ℂ))) from h_2554) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))) from (show @Eq M.Value _ _ from Eq.refl _)))) (show (M.number (2 : ℂ)) = (M.number (2 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)))))
                )
            )
          let _object_w129 := (let _wd_1_0 := (let _wd_2_0 := (let _wd_3_0 := (((_object_w128).val.left).val.base).val.left;
          let _wd_3_1 := (((_object_w127).val.left).val.base).val.right;
          (Litex.sub _wd_3_0 _wd_3_1 (by
            let _atomic_wd_1_0 := _wd_3_0
            exact (M.real_subset_complex _ (Litex.inOfSame (((_object_w127).val.left).val.base).val.left _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) h_2553 (show @Eq M.Value _ _ from Eq.refl _) h_2548))) (by
            let _atomic_wd_1_0 := _wd_3_1
            exact (M.real_subset_complex _ h_2545))));
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.subInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.inOfSame (((_object_w127).val.left).val.base).val.left (_atomic_wd_1_0).val.left (Litex.R (M := M)) (Litex.R (M := M)) h_2553 (show @Eq M.Value _ _ from Eq.refl _) h_2548) h_2545)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          let _wd_1_1 := (let _wd_2_0 := (let _wd_3_0 := (((_object_w128).val.right).val.base).val.left;
          let _wd_3_1 := (((_object_w127).val.right).val.base).val.right;
          (Litex.sub _wd_3_0 _wd_3_1 (by
            let _atomic_wd_1_0 := _wd_3_0
            exact (M.real_subset_complex _ (Litex.inOfSame (((_object_w127).val.right).val.base).val.left _atomic_wd_1_0 (Litex.R (M := M)) (Litex.R (M := M)) h_2554 (show @Eq M.Value _ _ from Eq.refl _) h_2549))) (by
            let _atomic_wd_1_0 := _wd_3_1
            exact (M.real_subset_complex _ h_2546))));
          let _wd_2_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.powNatReal _wd_2_0 _wd_2_1 (2 : ℕ) (by
            let _atomic_wd_1_0 := _wd_2_0
            exact (Litex.subInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.inOfSame (((_object_w127).val.right).val.base).val.left (_atomic_wd_1_0).val.left (Litex.R (M := M)) (Litex.R (M := M)) h_2554 (show @Eq M.Value _ _ from Eq.refl _) h_2549) h_2546)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber _wd_2_1 (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num))));
          (Litex.add _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.subInC ((_atomic_wd_1_0).val.base).val.left ((_atomic_wd_1_0).val.base).val.right (M.real_subset_complex _ (Litex.inOfSame (((_object_w127).val.left).val.base).val.left ((_atomic_wd_1_0).val.base).val.left (Litex.R (M := M)) (Litex.R (M := M)) h_2553 (show @Eq M.Value _ _ from Eq.refl _) h_2548)) (M.real_subset_complex _ h_2545))
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            )) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (by
              let _litex_power := _atomic_wd_1_0
              have _elaborated_power_base := (Litex.subInC ((_atomic_wd_1_0).val.base).val.left ((_atomic_wd_1_0).val.base).val.right (M.real_subset_complex _ (Litex.inOfSame (((_object_w127).val.right).val.base).val.left ((_atomic_wd_1_0).val.base).val.left (Litex.R (M := M)) (Litex.R (M := M)) h_2554 (show @Eq M.Value _ _ from Eq.refl _) h_2549)) (M.real_subset_complex _ h_2546))
              have _elaborated_power_exponent := (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))
              have _recorded_power_base : Litex.In _litex_power.val.base (Litex.C (M := M)) := _elaborated_power_base
              have _recorded_power_exponent : Litex.In _litex_power.val.exponent (Litex.Z (M := M)) := _elaborated_power_exponent
              exact Litex.powStructuralInC _litex_power _recorded_power_base _recorded_power_exponent
            ))))

          have h_2474 : (by
            let _equal_wd_1_0 := _object_w127
            let _equal_wd_1_1 := _object_w129
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (congrArg₂ M.addValue (show (M.powValue (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))) (M.number (2 : ℂ))) = (M.powValue (M.subValue (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))) (M.number (2 : ℂ))) from (congrArg₂ M.powValue (show (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))) = (M.subValue (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))) from (congrArg₂ M.subValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (1 : ℂ))) = (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ)))) (M.number (2 : ℂ))) from h_2553) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (1 : ℂ))) from (show @Eq M.Value _ _ from Eq.refl _)))) (show (M.number (2 : ℂ)) = (M.number (2 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)))) (show (M.powValue (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ)))) (M.number (2 : ℂ))) = (M.powValue (M.subValue (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ)))) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ)))) (M.number (2 : ℂ))) from (congrArg₂ M.powValue (show (M.subValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ)))) = (M.subValue (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ)))) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ)))) from (congrArg₂ M.subValue (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i24) (M.number (2 : ℂ))) = (M.divValue (M.addValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i22) (M.number (2 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ)))) (M.number (2 : ℂ))) from h_2554) (show (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i23) (M.number (2 : ℂ))) from (show @Eq M.Value _ _ from Eq.refl _)))) (show (M.number (2 : ℂ)) = (M.number (2 : ℂ)) from (show @Eq M.Value _ _ from Eq.refl _)))))
                )
            )
          have h_2475 : (by
            let _equal_wd_1_0 := _object_w128
            let _equal_wd_1_1 := _object_w129
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.NativeBridge.sameOfDenoteNumber _ _ ((((((Litex.NativeBridge.asComplex _object_h2542 (Litex.realToComplex _object_h2542 h_2542)) + (Litex.NativeBridge.asComplex _object_h2545 (Litex.realToComplex _object_h2545 h_2545))) / (2 : ℂ)) - (Litex.NativeBridge.asComplex _object_h2542 (Litex.realToComplex _object_h2542 h_2542))) ^ (2 : ℕ)) + (((((Litex.NativeBridge.asComplex _object_h2543 (Litex.realToComplex _object_h2543 h_2543)) + (Litex.NativeBridge.asComplex _object_h2546 (Litex.realToComplex _object_h2546 h_2546))) / (2 : ℂ)) - (Litex.NativeBridge.asComplex _object_h2543 (Litex.realToComplex _object_h2543 h_2543))) ^ (2 : ℕ))) ((((((Litex.NativeBridge.asComplex _object_h2542 (Litex.realToComplex _object_h2542 h_2542)) + (Litex.NativeBridge.asComplex _object_h2545 (Litex.realToComplex _object_h2545 h_2545))) / (2 : ℂ)) - (Litex.NativeBridge.asComplex _object_h2545 (Litex.realToComplex _object_h2545 h_2545))) ^ (2 : ℕ)) + (((((Litex.NativeBridge.asComplex _object_h2543 (Litex.realToComplex _object_h2543 h_2543)) + (Litex.NativeBridge.asComplex _object_h2546 (Litex.realToComplex _object_h2546 h_2546))) / (2 : ℂ)) - (Litex.NativeBridge.asComplex _object_h2546 (Litex.realToComplex _object_h2546 h_2546))) ^ (2 : ℕ))) (Litex.NativeBridge.denoteAdd (_object_w128).val.left (_object_w128).val.right (_object_w128).wd.1 (_object_w128).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal ((_object_w128).val.left).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                    let _atomic_wd_1_0 := ((_object_w128).val.left).val.base
                    exact (Litex.subInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.inOfSame (((_object_w127).val.left).val.base).val.left (_atomic_wd_1_0).val.left (Litex.R (M := M)) (Litex.R (M := M)) h_2553 (show @Eq M.Value _ _ from Eq.refl _) h_2548) h_2542)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteSub (((_object_w128).val.left).val.base).val.left (((_object_w128).val.left).val.base).val.right (((_object_w128).val.left).val.base).wd.1 (((_object_w128).val.left).val.base).wd.2 _ _ (Litex.NativeBridge.denoteDiv (Litex.add _object_h2542 _object_h2545 (Litex.realToComplex _object_h2542 h_2542) (Litex.realToComplex _object_h2545 h_2545)) (Litex.number (M := M) (2 : ℂ)) (Litex.addInC _object_h2542 _object_h2545 (Litex.realToComplex _object_h2542 h_2542) (Litex.realToComplex _object_h2545 h_2545)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.numberNonzero (M := M) (2 : ℂ) (by norm_num)) _ _ (Litex.NativeBridge.denoteAdd _object_h2542 _object_h2545 (Litex.realToComplex _object_h2542 h_2542) (Litex.realToComplex _object_h2545 h_2545) _ _ (Litex.NativeBridge.asComplex_spec _object_h2542 (Litex.realToComplex _object_h2542 h_2542)) (Litex.NativeBridge.asComplex_spec _object_h2545 (Litex.realToComplex _object_h2545 h_2545))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.asComplex_spec _object_h2542 (Litex.realToComplex _object_h2542 h_2542)))) (Litex.NativeBridge.denotePowNatReal ((_object_w128).val.right).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                    let _atomic_wd_1_0 := ((_object_w128).val.right).val.base
                    exact (Litex.subInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.inOfSame (((_object_w127).val.right).val.base).val.left (_atomic_wd_1_0).val.left (Litex.R (M := M)) (Litex.R (M := M)) h_2554 (show @Eq M.Value _ _ from Eq.refl _) h_2549) h_2543)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteSub (((_object_w128).val.right).val.base).val.left (((_object_w128).val.right).val.base).val.right (((_object_w128).val.right).val.base).wd.1 (((_object_w128).val.right).val.base).wd.2 _ _ (Litex.NativeBridge.denoteDiv (Litex.add _object_h2543 _object_h2546 (Litex.realToComplex _object_h2543 h_2543) (Litex.realToComplex _object_h2546 h_2546)) (Litex.number (M := M) (2 : ℂ)) (Litex.addInC _object_h2543 _object_h2546 (Litex.realToComplex _object_h2543 h_2543) (Litex.realToComplex _object_h2546 h_2546)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.numberNonzero (M := M) (2 : ℂ) (by norm_num)) _ _ (Litex.NativeBridge.denoteAdd _object_h2543 _object_h2546 (Litex.realToComplex _object_h2543 h_2543) (Litex.realToComplex _object_h2546 h_2546) _ _ (Litex.NativeBridge.asComplex_spec _object_h2543 (Litex.realToComplex _object_h2543 h_2543)) (Litex.NativeBridge.asComplex_spec _object_h2546 (Litex.realToComplex _object_h2546 h_2546))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.asComplex_spec _object_h2543 (Litex.realToComplex _object_h2543 h_2543))))) (Litex.NativeBridge.denoteAdd (_object_w129).val.left (_object_w129).val.right (_object_w129).wd.1 (_object_w129).wd.2 _ _ (Litex.NativeBridge.denotePowNatReal ((_object_w129).val.left).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                    let _atomic_wd_1_0 := ((_object_w129).val.left).val.base
                    exact (Litex.subInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.inOfSame (((_object_w127).val.left).val.base).val.left (_atomic_wd_1_0).val.left (Litex.R (M := M)) (Litex.R (M := M)) h_2553 (show @Eq M.Value _ _ from Eq.refl _) h_2548) h_2545)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteSub (((_object_w129).val.left).val.base).val.left (((_object_w129).val.left).val.base).val.right (((_object_w129).val.left).val.base).wd.1 (((_object_w129).val.left).val.base).wd.2 _ _ (Litex.NativeBridge.denoteDiv (Litex.add _object_h2542 _object_h2545 (Litex.realToComplex _object_h2542 h_2542) (Litex.realToComplex _object_h2545 h_2545)) (Litex.number (M := M) (2 : ℂ)) (Litex.addInC _object_h2542 _object_h2545 (Litex.realToComplex _object_h2542 h_2542) (Litex.realToComplex _object_h2545 h_2545)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.numberNonzero (M := M) (2 : ℂ) (by norm_num)) _ _ (Litex.NativeBridge.denoteAdd _object_h2542 _object_h2545 (Litex.realToComplex _object_h2542 h_2542) (Litex.realToComplex _object_h2545 h_2545) _ _ (Litex.NativeBridge.asComplex_spec _object_h2542 (Litex.realToComplex _object_h2542 h_2542)) (Litex.NativeBridge.asComplex_spec _object_h2545 (Litex.realToComplex _object_h2545 h_2545))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.asComplex_spec _object_h2545 (Litex.realToComplex _object_h2545 h_2545)))) (Litex.NativeBridge.denotePowNatReal ((_object_w129).val.right).val.base (Litex.number (M := M) (2 : ℂ)) (2 : ℕ) (by
                    let _atomic_wd_1_0 := ((_object_w129).val.right).val.base
                    exact (Litex.subInR (_atomic_wd_1_0).val.left (_atomic_wd_1_0).val.right (Litex.inOfSame (((_object_w127).val.right).val.base).val.left (_atomic_wd_1_0).val.left (Litex.R (M := M)) (Litex.R (M := M)) h_2554 (show @Eq M.Value _ _ from Eq.refl _) h_2549) h_2546)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.sameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) ((2 : ℕ) : ℂ)) (2 : ℂ) ((2 : ℕ) : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) ((2 : ℕ) : ℂ)) (by norm_num)) _ (Litex.NativeBridge.denoteSub (((_object_w129).val.right).val.base).val.left (((_object_w129).val.right).val.base).val.right (((_object_w129).val.right).val.base).wd.1 (((_object_w129).val.right).val.base).wd.2 _ _ (Litex.NativeBridge.denoteDiv (Litex.add _object_h2543 _object_h2546 (Litex.realToComplex _object_h2543 h_2543) (Litex.realToComplex _object_h2546 h_2546)) (Litex.number (M := M) (2 : ℂ)) (Litex.addInC _object_h2543 _object_h2546 (Litex.realToComplex _object_h2543 h_2543) (Litex.realToComplex _object_h2546 h_2546)) (Litex.numberInC (M := M) (2 : ℂ)) (Litex.NativeBridge.numberNonzero (M := M) (2 : ℂ) (by norm_num)) _ _ (Litex.NativeBridge.denoteAdd _object_h2543 _object_h2546 (Litex.realToComplex _object_h2543 h_2543) (Litex.realToComplex _object_h2546 h_2546) _ _ (Litex.NativeBridge.asComplex_spec _object_h2543 (Litex.realToComplex _object_h2543 h_2543)) (Litex.NativeBridge.asComplex_spec _object_h2546 (Litex.realToComplex _object_h2546 h_2546))) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ))) (Litex.NativeBridge.asComplex_spec _object_h2546 (Litex.realToComplex _object_h2546 h_2546))))) (by
                    have _litex_nz_0 : ((2 : ℂ) : ℂ) ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote (Litex.number (M := M) (2 : ℂ)) (2 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.notSameOfDenoteNumber (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (0 : ℂ)) (2 : ℂ) (0 : ℂ) (Litex.NativeBridge.denoteNumber (M := M) (2 : ℂ)) (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (by norm_num))
                    litex_normalize_rational (disch := repeat' first | exact _litex_nz_0 | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)
                  ))
                )
            )
          have h_2476 : (by
            let _equal_wd_1_0 := _object_w102
            let _equal_wd_1_1 := _object_w126
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  ((((((((h_2471).trans h_2473)).trans h_2475)).trans (h_2474).symm)).trans (h_2472).symm)
                )
            )
          exact h_2476
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_midpoint_x5f_equidistance_x2f_statement_x2e_lit
