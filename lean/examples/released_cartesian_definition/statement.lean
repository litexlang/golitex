import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_released_x5f_cartesian_x5f_definition_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_3 : (by
  let _equal_wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.Z (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.Z (M := M))) (fun i => Fin.elim0 i))))
  let _equal_wd_1_1 := (Litex.setBuilder (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_6 : Litex.In _value_i2 (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) => (by
    let _object_h7 := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
      exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))
    have h_7 : Litex.In _value_i2 _object_h7 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inOfSame _value_i2 _value_i2 (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
              exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) _object_h7 (Litex.sameRefl _value_i2) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
              exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) h_6)
          )
      )
    exact ∃ (h_1 : Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
    Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union (Litex.R (M := M)) (Litex.Z (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_7 (by
      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
      exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) (Litex.R (M := M))), Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
    Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union (Litex.R (M := M)) (Litex.Z (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_7 (by
      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
      exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) (Litex.Z (M := M))
  )))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.Z (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.Z (M := M))) (fun i => Fin.elim0 i))));
        let _equal_wd_1_1 := (Litex.setBuilder (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
          exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_6 : Litex.In _value_i2 (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
          exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) => (by
          let _object_h7 := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
            exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))
          have h_7 : Litex.In _value_i2 _object_h7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i2 _value_i2 (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
                    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) _object_h7 (Litex.sameRefl _value_i2) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
                    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) h_6)
                )
            )
          exact ∃ (h_1 : Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union (Litex.R (M := M)) (Litex.Z (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_7 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) (Litex.R (M := M))), Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union (Litex.R (M := M)) (Litex.Z (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_7 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) (Litex.Z (M := M))
        )));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from by
          let _cart := _equal_wd_1_0
          let _definition := _equal_wd_1_1
          let _bound := _definition.val.bound
          apply Litex.cartSameSetBuilder _cart _bound _definition.val.predicate (Litex.denote _bound.val.carrier)
          · exact Litex.denoteFiniteSeq _bound 2 (by change M.number (2 : ℂ) = M.number ((2 : ℕ) : ℂ); norm_num)
          · exact (by
          have _finiteProof_0 := ((show ∀ x, M.mem x (_cart.val.factors (0 : Fin 2)) → M.mem x (Litex.denote _bound.val.carrier) from fun _x _hx => (Litex.SetSemantics.union_members (M := M) _ _ _).mpr (Or.inl (_hx))))
          have _finiteProof_1 := ((show ∀ x, M.mem x (_cart.val.factors (1 : Fin 2)) → M.mem x (Litex.denote _bound.val.carrier) from fun _x _hx => (Litex.SetSemantics.union_members (M := M) _ _ _).mpr (Or.inr (_hx))))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )
          · intro _point _hin
            change (∃ _ : (M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _point) (M.number (1 : ℂ))) (_cart.val.factors (0 : Fin 2))), M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _point) (M.number (2 : ℂ))) (_cart.val.factors (1 : Fin 2))) ↔ _
            constructor
            · rintro ⟨_coord_0, _coord_1⟩
              exact (by
          have _finiteProof_0 := ((show M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _point) (Litex.FiniteFunction.index (0 : Fin 2))) (_cart.val.factors (0 : Fin 2)) from by
            have _index : Litex.FiniteFunction.index (M := M) (0 : Fin 2) = M.number (1 : ℂ) := by norm_num [Litex.FiniteFunction.index]
            rw [_index]
            exact _coord_0))
          have _finiteProof_1 := ((show M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _point) (Litex.FiniteFunction.index (1 : Fin 2))) (_cart.val.factors (1 : Fin 2)) from by
            have _index : Litex.FiniteFunction.index (M := M) (1 : Fin 2) = M.number (2 : ℂ) := by norm_num [Litex.FiniteFunction.index]
            rw [_index]
            exact _coord_1))
          exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
        )
            · intro _all
              exact ⟨(by
          have _index : Litex.FiniteFunction.index (M := M) (0 : Fin 2) = M.number (1 : ℂ) := by norm_num [Litex.FiniteFunction.index]
          rw [← _index]
          exact _all (0 : Fin 2)), (by
          have _index : Litex.FiniteFunction.index (M := M) (1 : Fin 2) = M.number (2 : ℂ) := by norm_num [Litex.FiniteFunction.index]
          rw [← _index]
          exact _all (1 : Fin 2))⟩)))
      )
  )

noncomputable def _object_w15 := (Litex.setBuilder (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.finiteSeq _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
  exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (fun (_value_i6 : Litex.Obj (M := M) M.Value) (h_65 : Litex.In _value_i6 (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
(Litex.finiteSeq _wd_1_0 _wd_1_1 (by
  let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
  exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) => (by
  let _object_h66 := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))
  have h_66 : Litex.In _value_i6 _object_h66 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i6 _value_i6 (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
            exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) _object_h66 (Litex.sameRefl _value_i6) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
            exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) h_65)
        )
    )
  exact ∃ (h_60 : Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
  Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union (Litex.R (M := M)) (Litex.Z (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _value_i6 _litex_call_arg_0 h_66 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) (Litex.R (M := M))), Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
  Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union (Litex.R (M := M)) (Litex.Z (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i7 : M.Value) => True) _litex_input) _value_i6 _litex_call_arg_0 h_66 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) (Litex.Z (M := M))
)))

theorem h_62 : (by
  let _equal_wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.Z (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.Z (M := M))) (fun i => Fin.elim0 i))))
  let _equal_wd_1_1 := (_object_w15 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.Z (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.Z (M := M))) (fun i => Fin.elim0 i))));
        let _equal_wd_1_1 := (_object_w15 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((Litex.sameRefl _equal_wd_1_0)).symm.trans (((h_3 (M := M))).trans (by
          let _left := (Litex.setBuilder (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
          exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (fun (_value_i2 : Litex.Obj (M := M) M.Value) (h_6 : Litex.In _value_i2 (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
          exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) => (by
          let _object_h7 := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
            exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))
          have h_7 : Litex.In _value_i2 _object_h7 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i2 _value_i2 (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
                    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) _object_h7 (Litex.sameRefl _value_i2) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
                    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) h_6)
                )
            )
          exact ∃ (h_1 : Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union (Litex.R (M := M)) (Litex.Z (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_7 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) (Litex.R (M := M))), Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union (Litex.R (M := M)) (Litex.Z (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i3 : M.Value) => True) _litex_input) _value_i2 _litex_call_arg_0 h_7 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) (Litex.Z (M := M))
        )))
          let _right := _equal_wd_1_1
          exact (show Litex.Same _left _right from rfl))))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_released_x5f_cartesian_x5f_definition_x2f_statement_x2e_lit
