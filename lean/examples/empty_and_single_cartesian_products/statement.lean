import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_empty_x5f_and_x5f_single_x5f_cartesian_x5f_products_x2f_statement_x2e_lit

universe u
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_1 : (by
  let _equal_wd_1_0 := (Litex.cart (M := M) ![] (fun i => Fin.elim0 i))
  let _equal_wd_1_1 := (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
    _setTail_0);
  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
      _setTail_0)
    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num))))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (Litex.cart (M := M) ![] (fun i => Fin.elim0 i));
        let _equal_wd_1_1 := (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
          _setTail_0);
        let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
        (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
            _setTail_0)
          exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num))));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from by
          let _cart := _equal_wd_1_0
          let _definition := _equal_wd_1_1
          exact Litex.cartZeroSame _cart _definition (Litex.denoteFiniteSeq _definition 0 (by change M.number (0 : ℂ) = M.number ((0 : ℕ) : ℂ); norm_num)))))
      )
  )

theorem h_13 : (by
  let _equal_wd_1_0 := (Litex.cart (M := M) ![] (fun i => Fin.elim0 i))
  let _equal_wd_1_1 := (let _wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
    _setTail_0);
  let _wd_1_1 := (Litex.number (M := M) (0 : ℂ));
  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (let _setTail_0 := Litex.emptySet (M := M);
      _setTail_0)
    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (0 : ℂ) (0 : ℕ) (by norm_num))))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (h_1 (M := M))
      )
  )

theorem h_16 : (by
  let _equal_wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))
  let _equal_wd_1_1 := (Litex.setBuilder (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num))) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_19 : Litex.In _value_i4 (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) => (by
    let _object_h20 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))))
    have h_20 : Litex.In _value_i4 _object_h20 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inOfSame _value_i4 _value_i4 (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num))) _object_h20 (Litex.sameRefl _value_i4) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) h_19)
          )
      )
    exact Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
    Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_20 (by
      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))
      exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (1 : ℂ) (1 : ℂ) (1 : ℤ) (1 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) (Litex.R (M := M))
  )))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)));
        let _equal_wd_1_1 := (Litex.setBuilder (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num))) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_19 : Litex.In _value_i4 (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) => (by
          let _object_h20 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))))
          have h_20 : Litex.In _value_i4 _object_h20 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i4 _value_i4 (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num))) _object_h20 (Litex.sameRefl _value_i4) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) h_19)
                )
            )
          exact Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_20 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (1 : ℂ) (1 : ℂ) (1 : ℤ) (1 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) (Litex.R (M := M))
        )));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from by
          let _cart := _equal_wd_1_0
          let _definition := _equal_wd_1_1
          let _bound := _definition.val.bound
          apply Litex.cartSameSetBuilder _cart _bound _definition.val.predicate (Litex.denote _bound.val.carrier)
          · exact Litex.denoteFiniteSeq _bound 1 (by change M.number (1 : ℂ) = M.number ((1 : ℕ) : ℂ); norm_num)
          · exact (by
          have _finiteProof_0 := ((show ∀ x, M.mem x (_cart.val.factors (0 : Fin 1)) → M.mem x (Litex.denote _bound.val.carrier) from fun _x _hx => _hx))
          exact (Fin.cases _finiteProof_0 (fun i => Fin.elim0 i))
        )
          · intro _point _hin
            change (M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _point) (M.number (1 : ℂ))) (_cart.val.factors (0 : Fin 1))) ↔ _
            constructor
            · intro _coord_0
              exact (by
          have _finiteProof_0 := ((show M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _point) (Litex.FiniteFunction.index (0 : Fin 1))) (_cart.val.factors (0 : Fin 1)) from by
            have _index : Litex.FiniteFunction.index (M := M) (0 : Fin 1) = M.number (1 : ℂ) := by norm_num [Litex.FiniteFunction.index]
            rw [_index]
            exact _coord_0))
          exact (Fin.cases _finiteProof_0 (fun i => Fin.elim0 i))
        )
            · intro _all
              exact (by
          have _index : Litex.FiniteFunction.index (M := M) (0 : Fin 1) = M.number (1 : ℂ) := by norm_num [Litex.FiniteFunction.index]
          rw [← _index]
          exact _all (0 : Fin 1)))))
      )
  )

noncomputable def _object_w13 := (Litex.setBuilder (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num))) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_52 : Litex.In _value_i8 (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) => (by
  let _object_h53 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))))
  have h_53 : Litex.In _value_i8 _object_h53 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i8 _value_i8 (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num))) _object_h53 (Litex.sameRefl _value_i8) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) h_52)
        )
    )
  exact Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
  Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i8 _litex_call_arg_0 h_53 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (1 : ℂ) (1 : ℂ) (1 : ℤ) (1 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) (Litex.R (M := M))
)))

theorem h_49 : (by
  let _equal_wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)))
  let _equal_wd_1_1 := (_object_w13 (M := M))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (let _equal_wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (fun i => Fin.elim0 i)));
        let _equal_wd_1_1 := (_object_w13 (M := M));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((Litex.sameRefl _equal_wd_1_0)).symm.trans (((h_16 (M := M))).trans (by
          let _left := (Litex.setBuilder (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num))) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_19 : Litex.In _value_i4 (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) => (by
          let _object_h20 := (Litex.fnSet (Litex.finiteSeqSignature (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))))
          have h_20 : Litex.In _value_i4 _object_h20 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i4 _value_i4 (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num))) _object_h20 (Litex.sameRefl _value_i4) (Litex.finiteSeq_eq_fnSet (Litex.finiteSeq (Litex.R (M := M)) (Litex.number (M := M) (1 : ℂ)) (Litex.isSet (Litex.R (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (1 : ℂ) (1 : ℕ) (by norm_num)))) h_19)
                )
            )
          exact Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num))) (Litex.R (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_20 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (1 : ℂ) (1 : ℂ) (1 : ℤ) (1 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) (Litex.R (M := M))
        )))
          let _right := _equal_wd_1_1
          exact (show Litex.Same _left _right from rfl))))))
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_empty_x5f_and_x5f_single_x5f_cartesian_x5f_products_x2f_statement_x2e_lit
