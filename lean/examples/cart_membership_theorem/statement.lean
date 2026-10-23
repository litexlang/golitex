import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_cart_x5f_membership_x5f_theorem_x2f_statement_x2e_lit

universe u v3
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_1 : Litex.In (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (2 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (fun i => Fin.elim0 i)))) (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) :=
  (by
    let _membership_function := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (2 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (fun i => Fin.elim0 i))))
    let _membership_target := (by
      have _checked_header : ∀ (_raw_i1 : M.Value), M.mem _raw_i1 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) → ((fun (_raw_i1 : M.Value) => True) _raw_i1) → True := by
        intro _raw_i1 h_7 _
        let _value_i1 := Litex.semanticObject (M := M) _raw_i1 (M.member_isSet h_7)
        have h_7 : Litex.In _value_i1 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) := h_7
        exact True.intro
      exact Litex.fnSet (Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.denote (Litex.union (Litex.R (M := M)) (Litex.R (M := M)))) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.isSet (Litex.union (Litex.R (M := M)) (Litex.R (M := M)))) (fun (_litex_input : M.Value) => (fun (_raw_i1 : M.Value) => True) _litex_input)))
    have h_2 : (by
      let _equal_wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
      let _equal_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
      exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (show @Eq M.Value _ _ from Eq.refl _)
          )
      )
    have h_3 : Litex.In (Litex.number (M := M) (1 : ℂ)) (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.NativeBridge.numberInROfEq (M := M) (1 : ℂ) (1 : ℝ) (by norm_num))
          )
      )
    have h_4 : Litex.In (Litex.number (M := M) (2 : ℂ)) (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.NativeBridge.numberInROfEq (M := M) (2 : ℂ) (2 : ℝ) (by norm_num))
          )
      )
    exact (by
    let _source_cart := (Litex.tupleSingletonCart (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (2 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (fun i => Fin.elim0 i)))))
    have _source_member : Litex.In _membership_function _source_cart := (by
    let _tuple := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (2 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (fun i => Fin.elim0 i))))
    let _receiver := (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (2 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (fun i => Fin.elim0 i))))
    have _same : Litex.Same _receiver _tuple := (show @Eq M.Value _ _ from Eq.refl _)
    exact Litex.inOfSame _tuple _receiver (Litex.tupleSingletonCart _tuple) (Litex.tupleSingletonCart _tuple) _same.symm (Litex.sameRefl _) (Litex.tupleInSingletonCart _tuple))
    let _cart := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
    let _target := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
    have _coordinates : ∀ i : Fin 2, M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) (Litex.FiniteFunction.index i)) (_cart.val.factors i) := (by
    have _finiteProof_0 := ((show M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) (Litex.FiniteFunction.index (0 : Fin 2))) (Litex.denote (Litex.R (M := M))) from by
      have _coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) (Litex.FiniteFunction.index (0 : Fin 2)) = (M.number (1 : ℂ)) := ((congrArg (fun _p => Litex.FunctionSemantics.callValue (M := M) _p (Litex.FiniteFunction.index (0 : Fin 2))) (show @Eq M.Value _ _ from Eq.refl _)).trans (Litex.tuple_coordinate (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (2 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (fun i => Fin.elim0 i)))) (0 : Fin 2)))
      rw [_coordinate]
      exact h_3))
    have _finiteProof_1 := ((show M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) (Litex.FiniteFunction.index (1 : Fin 2))) (Litex.denote (Litex.R (M := M))) from by
      have _coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) (Litex.FiniteFunction.index (1 : Fin 2)) = (M.number (2 : ℂ)) := ((congrArg (fun _p => Litex.FunctionSemantics.callValue (M := M) _p (Litex.FiniteFunction.index (1 : Fin 2))) (show @Eq M.Value _ _ from Eq.refl _)).trans (Litex.tuple_coordinate (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (2 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (fun i => Fin.elim0 i)))) (1 : Fin 2)))
      rw [_coordinate]
      exact h_4))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )
    have _member : Litex.In _membership_function _cart := Litex.FiniteFunction.cart_of_coordinates _source_member _coordinates
    have _carrier_same : Litex.Same _target _cart := h_2
    exact Litex.inOfSame _membership_function _membership_function _cart _target (Litex.sameRefl _) _carrier_same.symm _member)
  )

noncomputable def _object_h17 := (Litex.number (M := M) (1 : ℂ))

theorem h_17 : Litex.In (_object_h17 (M := M)) (Litex.R (M := M)) :=
  (Litex.tuple_coordinate_mem (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (2 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (fun i => Fin.elim0 i)))) (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) (h_1 (M := M)) (0 : Fin 2))

noncomputable def _object_h18 := (Litex.number (M := M) (2 : ℂ))

theorem h_18 : Litex.In (_object_h18 (M := M)) (Litex.R (M := M)) :=
  (Litex.tuple_coordinate_mem (Litex.tuple (M := M) ![Litex.denote (Litex.number (M := M) (1 : ℂ)), Litex.denote (Litex.number (M := M) (2 : ℂ))] (Fin.cases (Litex.isSet (Litex.number (M := M) (1 : ℂ))) (Fin.cases (Litex.isSet (Litex.number (M := M) (2 : ℂ))) (fun i => Fin.elim0 i)))) (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) (h_1 (M := M)) (1 : Fin 2))

theorem h_20 : ∀ {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_22 : Litex.In _value_i3 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))), (by
  let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.C (M := M)), Litex.denote (Litex.C (M := M))] (Fin.cases (Litex.isSet (Litex.C (M := M))) (Fin.cases (Litex.isSet (Litex.C (M := M))) (fun i => Fin.elim0 i))))
  exact Litex.In _value_i3 _atomic_wd_1_1) :=
  (by
    intro _Host_i3 _rep_i3 _value_i3 h_22
    let _object_h23 := (Litex.cartCall _value_i3 _ (Litex.number (M := M) (1 : ℂ)) h_22 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_23 : Litex.In _object_h23 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_22 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h24 := (Litex.cartCall _value_i3 _ (Litex.number (M := M) (2 : ℂ)) h_22 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_24 : Litex.In _object_h24 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_22 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    have h_32 : Litex.In _value_i3 (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))) :=
      (by
        litex_checked_step =>
          exact (
            h_22
          )
      )
    let _object_h33 := (Litex.cartCall _value_i3 _ (Litex.number (M := M) (1 : ℂ)) h_32 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
    have h_33 : Litex.In _object_h33 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_32 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )
    let _object_h34 := (Litex.cartCall _value_i3 _ (Litex.number (M := M) (2 : ℂ)) h_32 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
    have h_34 : Litex.In _object_h34 (Litex.R (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_32 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    have h_21 : (by
      let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.C (M := M)), Litex.denote (Litex.C (M := M))] (Fin.cases (Litex.isSet (Litex.C (M := M))) (Fin.cases (Litex.isSet (Litex.C (M := M))) (fun i => Fin.elim0 i))))
      exact Litex.In _value_i3 _atomic_wd_1_1) :=
      (by
        litex_checked_step =>
          exact (
            (by
              let _membership_function := _value_i3
              let _membership_target := (by
                have _checked_header : ∀ (_raw_i5 : M.Value), M.mem _raw_i5 (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) → ((fun (_raw_i5 : M.Value) => True) _raw_i5) → True := by
                  intro _raw_i5 h_69 _
                  let _value_i5 := Litex.semanticObject (M := M) _raw_i5 (M.member_isSet h_69)
                  have h_69 : Litex.In _value_i5 (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) := h_69
                  exact True.intro
                exact Litex.fnSet (Litex.FunctionSignature.withGuard (M := M) (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.denote (Litex.union (Litex.C (M := M)) (Litex.C (M := M)))) (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))) (Litex.isSet (Litex.union (Litex.C (M := M)) (Litex.C (M := M)))) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input)))
              have h_36 : (by
                let _equal_wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.C (M := M)), Litex.denote (Litex.C (M := M))] (Fin.cases (Litex.isSet (Litex.C (M := M))) (Fin.cases (Litex.isSet (Litex.C (M := M))) (fun i => Fin.elim0 i))))
                let _equal_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.C (M := M)), Litex.denote (Litex.C (M := M))] (Fin.cases (Litex.isSet (Litex.C (M := M))) (Fin.cases (Litex.isSet (Litex.C (M := M))) (fun i => Fin.elim0 i))))
                exact Litex.Same _equal_wd_1_1 _equal_wd_1_1) :=
                (by
                  litex_checked_step =>
                    exact (
                      (show @Eq M.Value _ _ from Eq.refl _)
                    )
                )
              have h_37 : (by
                let _atomic_wd_1_0 := _object_h33
                exact Litex.In _atomic_wd_1_0 (Litex.C (M := M))) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        let _atomic_wd_1_0 := _object_h33
                        exact (M.real_subset_complex _ h_33))
                    )
                )
              have h_38 : (by
                let _atomic_wd_1_0 := _object_h34
                exact Litex.In _atomic_wd_1_0 (Litex.C (M := M))) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        let _atomic_wd_1_0 := _object_h34
                        exact (M.real_subset_complex _ h_34))
                    )
                )
              have h_35 : Litex.In _value_i3 (Litex.cart (M := M) ![Litex.denote (Litex.C (M := M)), Litex.denote (Litex.C (M := M))] (Fin.cases (Litex.isSet (Litex.C (M := M))) (Fin.cases (Litex.isSet (Litex.C (M := M))) (fun i => Fin.elim0 i)))) :=
                (by
                  litex_checked_step =>
                    exact (
                      (by
                        let _source_cart := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i))))
                        have _source_member : Litex.In _membership_function _source_cart := h_32
                        let _cart := (Litex.cart (M := M) ![Litex.denote (Litex.C (M := M)), Litex.denote (Litex.C (M := M))] (Fin.cases (Litex.isSet (Litex.C (M := M))) (Fin.cases (Litex.isSet (Litex.C (M := M))) (fun i => Fin.elim0 i))))
                        let _target := (Litex.cart (M := M) ![Litex.denote (Litex.C (M := M)), Litex.denote (Litex.C (M := M))] (Fin.cases (Litex.isSet (Litex.C (M := M))) (Fin.cases (Litex.isSet (Litex.C (M := M))) (fun i => Fin.elim0 i))))
                        have _coordinates : ∀ i : Fin 2, M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) (Litex.FiniteFunction.index i)) (_cart.val.factors i) := (by
                        have _finiteProof_0 := ((show M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) (Litex.FiniteFunction.index (0 : Fin 2))) (Litex.denote (Litex.C (M := M))) from by
                          have _coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) (Litex.FiniteFunction.index (0 : Fin 2)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (M.number (1 : ℂ))) := (by
                          have _index : Litex.FiniteFunction.index (M := M) (0 : Fin 2) = M.number (1 : ℂ) := by norm_num [Litex.FiniteFunction.index]
                          exact congrArg (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function)) _index)
                          rw [_coordinate]
                          exact h_37))
                        have _finiteProof_1 := ((show M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) (Litex.FiniteFunction.index (1 : Fin 2))) (Litex.denote (Litex.C (M := M))) from by
                          have _coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function) (Litex.FiniteFunction.index (1 : Fin 2)) = (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i3) (M.number (2 : ℂ))) := (by
                          have _index : Litex.FiniteFunction.index (M := M) (1 : Fin 2) = M.number (2 : ℂ) := by norm_num [Litex.FiniteFunction.index]
                          exact congrArg (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _membership_function)) _index)
                          rw [_coordinate]
                          exact h_38))
                        exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                      )
                        have _member : Litex.In _membership_function _cart := Litex.FiniteFunction.cart_of_coordinates _source_member _coordinates
                        have _carrier_same : Litex.Same _target _cart := h_36
                        exact Litex.inOfSame _membership_function _membership_function _cart _target (Litex.sameRefl _) _carrier_same.symm _member)
                    )
                )
              let _object_h235 := (Litex.cartCall _value_i3 _ (Litex.number (M := M) (1 : ℂ)) h_35 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))
              have h_235 : Litex.In _object_h235 (Litex.C (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.FiniteFunction.coordinate_mem_number (M := M) h_35 (0 : Fin 2) (1 : ℂ) (by norm_num))
                    )
                )
              let _object_h236 := (Litex.cartCall _value_i3 _ (Litex.number (M := M) (2 : ℂ)) h_35 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))
              have h_236 : Litex.In _object_h236 (Litex.C (M := M)) :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.FiniteFunction.coordinate_mem_number (M := M) h_35 (1 : Fin 2) (2 : ℂ) (by norm_num))
                    )
                )
              exact (by
              let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.C (M := M)), Litex.denote (Litex.C (M := M))] (Fin.cases (Litex.isSet (Litex.C (M := M))) (Fin.cases (Litex.isSet (Litex.C (M := M))) (fun i => Fin.elim0 i))))
              exact h_35)
            )
          )
      )

    let _object_h248 := (Litex.cartCall _value_i3 _ (Litex.number (M := M) (1 : ℂ)) h_21 (by change M.mem (M.number (1 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (0 : Fin 2))))

    have h_248 : Litex.In _object_h248 (Litex.C (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_21 (0 : Fin 2) (1 : ℂ) (by norm_num))
          )
      )

    let _object_h249 := (Litex.cartCall _value_i3 _ (Litex.number (M := M) (2 : ℂ)) h_21 (by change M.mem (M.number (2 : ℂ)) (Litex.FiniteFunction.indexSet 2); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) (1 : Fin 2))))

    have h_249 : Litex.In _object_h249 (Litex.C (M := M)) :=
      (by
        litex_checked_step =>
          exact (
            (Litex.FiniteFunction.coordinate_mem_number (M := M) h_21 (1 : Fin 2) (2 : ℂ) (by norm_num))
          )
      )
    exact (by
      let _atomic_wd_1_1 := (Litex.cart (M := M) ![Litex.denote (Litex.C (M := M)), Litex.denote (Litex.C (M := M))] (Fin.cases (Litex.isSet (Litex.C (M := M))) (Fin.cases (Litex.isSet (Litex.C (M := M))) (fun i => Fin.elim0 i))))
      exact h_21)
  )
end LitexCompiled.file_lean_x2f_examples_x2f_cart_x5f_membership_x5f_theorem_x2f_statement_x2e_lit
