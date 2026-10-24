import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_local_x5f_cartesian_x5f_definition_x2f_statement_x2e_lit

universe u v1 v2
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_4 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_8 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_9 : Litex.IsSet _value_i2), (by
  let _equal_wd_1_0 := (Litex.cart (M := M) ![Litex.denote _value_i1, Litex.denote _value_i2] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i2) (fun i => Fin.elim0 i))))
  let _equal_wd_1_1 := (Litex.setBuilder (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_20 : Litex.In _value_i3 (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) => (by
    let _object_h21 := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
      exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))
    have h_21 : Litex.In _value_i3 _object_h21 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inOfSame _value_i3 _value_i3 (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
              exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) _object_h21 (Litex.sameRefl _value_i3) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
              exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) h_20)
          )
      )
    exact ∃ (h_1 : Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
    Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union _value_i1 _value_i2) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_21 (by
      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
      exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) _value_i1), Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
    Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union _value_i1 _value_i2) (fun (_litex_input : M.Value) => (fun (_raw_i6 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_21 (by
      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
      exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) _value_i2
  )))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_8 _Host_i2 _rep_i2 _value_i2 h_9
          have h_63 : Litex.IsSet _value_i1 :=
            (by
              litex_checked_step =>
                exact (
                  h_8
                )
            )
          have h_64 : Litex.IsSet _value_i2 :=
            (by
              litex_checked_step =>
                exact (
                  h_9
                )
            )
          have h_67 : (by
            let _equal_wd_1_0 := (Litex.cart (M := M) ![Litex.denote _value_i1, Litex.denote _value_i2] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i2) (fun i => Fin.elim0 i))))
            let _equal_wd_1_1 := (Litex.setBuilder (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
              exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_78 : Litex.In _value_i8 (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
              exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) => (by
              let _object_h79 := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
              let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
              (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
                exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))
              have h_79 : Litex.In _value_i8 _object_h79 :=
                (by
                  litex_checked_step =>
                    exact (
                      (Litex.inOfSame _value_i8 _value_i8 (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
                      let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                      (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                        let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
                        exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) _object_h79 (Litex.sameRefl _value_i8) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
                      let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                      (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                        let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
                        exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) h_78)
                    )
                )
              exact ∃ (h_65 : Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
              Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union _value_i1 _value_i2) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i8 _litex_call_arg_0 h_79 (by
                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
                exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) _value_i1), Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
              Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union _value_i1 _value_i2) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i8 _litex_call_arg_0 h_79 (by
                let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
                exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) _value_i2
            )))
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := (Litex.cart (M := M) ![Litex.denote _value_i1, Litex.denote _value_i2] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i2) (fun i => Fin.elim0 i))));
                  let _equal_wd_1_1 := (Litex.setBuilder (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
                    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_78 : Litex.In _value_i8 (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
                    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) => (by
                    let _object_h79 := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
                      exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))
                    have h_79 : Litex.In _value_i8 _object_h79 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inOfSame _value_i8 _value_i8 (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
                            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                            (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
                              exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) _object_h79 (Litex.sameRefl _value_i8) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
                            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                            (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
                              exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) h_78)
                          )
                      )
                    exact ∃ (h_65 : Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
                    Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union _value_i1 _value_i2) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i8 _litex_call_arg_0 h_79 (by
                      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
                      exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) _value_i1), Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
                    Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union _value_i1 _value_i2) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i8 _litex_call_arg_0 h_79 (by
                      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
                      exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) _value_i2
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
          let _object_w15 := (Litex.setBuilder (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
            exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_142 : Litex.In _value_i4 (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
            exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) => (by
            let _object_h143 := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
              exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))
            have h_143 : Litex.In _value_i4 _object_h143 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inOfSame _value_i4 _value_i4 (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
                      exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) _object_h143 (Litex.sameRefl _value_i4) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
                      exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) h_142)
                  )
              )
            exact ∃ (h_5 : Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
            Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union _value_i1 _value_i2) (fun (_litex_input : M.Value) => (fun (_raw_i12 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_143 (by
              let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
              exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) _value_i1), Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
            Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union _value_i1 _value_i2) (fun (_litex_input : M.Value) => (fun (_raw_i12 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_143 (by
              let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
              exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) _value_i2
          )))

          have h_7 : (by
            let _equal_wd_1_0 := (Litex.cart (M := M) ![Litex.denote _value_i1, Litex.denote _value_i2] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i2) (fun i => Fin.elim0 i))))
            let _equal_wd_1_1 := _object_w15
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := (Litex.cart (M := M) ![Litex.denote _value_i1, Litex.denote _value_i2] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i2) (fun i => Fin.elim0 i))));
                  let _equal_wd_1_1 := _object_w15;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((Litex.sameRefl _equal_wd_1_0)).symm.trans ((h_67).trans (by
                    let _left := (Litex.setBuilder (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
                    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_78 : Litex.In _value_i8 (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
                    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) => (by
                    let _object_h79 := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
                      exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))
                    have h_79 : Litex.In _value_i8 _object_h79 :=
                      (by
                        litex_checked_step =>
                          exact (
                            (Litex.inOfSame _value_i8 _value_i8 (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
                            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                            (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
                              exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) _object_h79 (Litex.sameRefl _value_i8) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
                            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                            (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                              let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
                              exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) h_78)
                          )
                      )
                    exact ∃ (h_65 : Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
                    Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union _value_i1 _value_i2) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i8 _litex_call_arg_0 h_79 (by
                      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
                      exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) _value_i1), Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
                    Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union _value_i1 _value_i2) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i8 _litex_call_arg_0 h_79 (by
                      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
                      exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) _value_i2
                  )))
                    let _right := _equal_wd_1_1
                    exact (show Litex.Same _left _right from rfl))))))
                )
            )
          exact (let _equal_wd_1_0 := (Litex.cart (M := M) ![Litex.denote _value_i1, Litex.denote _value_i2] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i2) (fun i => Fin.elim0 i))));
          let _equal_wd_1_1 := (Litex.setBuilder (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
            exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_203 : Litex.In _value_i3 (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
            exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) => (by
            let _object_h204 := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
              exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))
            have h_204 : Litex.In _value_i3 _object_h204 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inOfSame _value_i3 _value_i3 (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
                      exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) _object_h204 (Litex.sameRefl _value_i3) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
                      exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) h_203)
                  )
              )
            exact ∃ (h_1 : Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
            Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union _value_i1 _value_i2) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_204 (by
              let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
              exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) _value_i1), Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
            Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union _value_i1 _value_i2) (fun (_litex_input : M.Value) => (fun (_raw_i13 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_204 (by
              let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
              exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) _value_i2
          )));
          (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((Litex.sameRefl _equal_wd_1_0)).symm.trans ((h_67).trans (by
            let _left := (Litex.setBuilder (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
            exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (fun (_value_i8 : Litex.Obj (M := M) M.Value) (h_78 : Litex.In _value_i8 (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
            exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) => (by
            let _object_h79 := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
              exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))
            have h_79 : Litex.In _value_i8 _object_h79 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inOfSame _value_i8 _value_i8 (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
                      exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) _object_h79 (Litex.sameRefl _value_i8) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := (Litex.union _value_i1 _value_i2)
                      exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) h_78)
                  )
              )
            exact ∃ (h_65 : Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
            Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union _value_i1 _value_i2) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i8 _litex_call_arg_0 h_79 (by
              let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
              exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) _value_i1), Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
            Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union _value_i1 _value_i2) (fun (_litex_input : M.Value) => (fun (_raw_i9 : M.Value) => True) _litex_input) _value_i8 _litex_call_arg_0 h_79 (by
              let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
              exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) _value_i2
          )))
            let _right := _equal_wd_1_1
            exact (show Litex.Same _left _right from rfl))))))
        )
      )
  )

theorem h_311 : (by
  let _equal_wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.Z (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.Z (M := M))) (fun i => Fin.elim0 i))))
  let _equal_wd_1_1 := (Litex.setBuilder (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (fun (_value_i15 : Litex.Obj (M := M) M.Value) (h_384 : Litex.In _value_i15 (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) => (by
    let _object_h385 := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
      exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))
    have h_385 : Litex.In _value_i15 _object_h385 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inOfSame _value_i15 _value_i15 (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
              exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) _object_h385 (Litex.sameRefl _value_i15) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
              exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) h_384)
          )
      )
    exact ∃ (h_309 : Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
    Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union (Litex.R (M := M)) (Litex.Z (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) => True) _litex_input) _value_i15 _litex_call_arg_0 h_385 (by
      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
      exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) (Litex.R (M := M))), Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
    Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union (Litex.R (M := M)) (Litex.Z (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) => True) _litex_input) _value_i15 _litex_call_arg_0 h_385 (by
      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
      exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) (Litex.Z (M := M))
  )))
  exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
  (by
    litex_complete =>
      exact (
        (by
          have h_312 : Litex.IsSet (Litex.R (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.isSet (Litex.R (M := M)))
                )
            )
          have h_313 : Litex.IsSet (Litex.Z (M := M)) :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.isSet (Litex.Z (M := M)))
                )
            )
          have h_314 : Litex.Same (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.Z (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.Z (M := M))) (fun i => Fin.elim0 i)))) (Litex.setBuilder (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
            exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_331 : Litex.In _value_i3 (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
            exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) => (by
            let _object_h332 := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
              exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))
            have h_332 : Litex.In _value_i3 _object_h332 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inOfSame _value_i3 _value_i3 (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
                      exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) _object_h332 (Litex.sameRefl _value_i3) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
                      exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) h_331)
                  )
              )
            exact ∃ (h_315 : Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
            Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union (Litex.R (M := M)) (Litex.Z (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_332 (by
              let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
              exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) (Litex.R (M := M))), Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
            Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union (Litex.R (M := M)) (Litex.Z (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_332 (by
              let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
              exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) (Litex.Z (M := M))
          ))) :=
            (by
              litex_checked_step =>
                exact (
                  ((h_4 (M := M)) (Litex.R (M := M)) h_312 (Litex.Z (M := M)) h_313)
                )
            )
          exact (let _equal_wd_1_0 := (Litex.cart (M := M) ![Litex.denote (Litex.R (M := M)), Litex.denote (Litex.Z (M := M))] (Fin.cases (Litex.isSet (Litex.R (M := M))) (Fin.cases (Litex.isSet (Litex.Z (M := M))) (fun i => Fin.elim0 i))));
        let _equal_wd_1_1 := (Litex.setBuilder (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
          exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (fun (_value_i15 : Litex.Obj (M := M) M.Value) (h_384 : Litex.In _value_i15 (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
          exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) => (by
          let _object_h385 := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
            exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))
          have h_385 : Litex.In _value_i15 _object_h385 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i15 _value_i15 (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
                    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) _object_h385 (Litex.sameRefl _value_i15) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
                    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) h_384)
                )
            )
          exact ∃ (h_309 : Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union (Litex.R (M := M)) (Litex.Z (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) => True) _litex_input) _value_i15 _litex_call_arg_0 h_385 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) (Litex.R (M := M))), Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union (Litex.R (M := M)) (Litex.Z (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i17 : M.Value) => True) _litex_input) _value_i15 _litex_call_arg_0 h_385 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) (Litex.Z (M := M))
        )));
        (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((Litex.sameRefl _equal_wd_1_0)).symm.trans ((h_314).trans (by
          let _left := (Litex.setBuilder (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
          exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (fun (_value_i3 : Litex.Obj (M := M) M.Value) (h_331 : Litex.In _value_i3 (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
        let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
        (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
          let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
          exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) => (by
          let _object_h332 := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
            exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))
          have h_332 : Litex.In _value_i3 _object_h332 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i3 _value_i3 (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
                    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) _object_h332 (Litex.sameRefl _value_i3) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)));
                  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                    let _atomic_wd_1_0 := (Litex.union (Litex.R (M := M)) (Litex.Z (M := M)))
                    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) h_331)
                )
            )
          exact ∃ (h_315 : Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union (Litex.R (M := M)) (Litex.Z (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_332 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) (Litex.R (M := M))), Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
          Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union (Litex.R (M := M)) (Litex.Z (M := M))) (fun (_litex_input : M.Value) => (fun (_raw_i16 : M.Value) => True) _litex_input) _value_i3 _litex_call_arg_0 h_332 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) (Litex.Z (M := M))
        )))
          let _right := _equal_wd_1_1
          exact (show Litex.Same _left _right from rfl))))))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_local_x5f_cartesian_x5f_definition_x2f_statement_x2e_lit
