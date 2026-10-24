import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_generic_x5f_cartesian_x5f_definitions_x2f_statement_x2e_lit

universe u v1 v2 v3 v8 v9
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_5 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_6 : Litex.IsSet _value_i1) {_Host_i2 : Type v2} [_rep_i2 : Litex.Representation M _Host_i2] (_value_i2 : Litex.Obj (M := M) _Host_i2) (h_7 : Litex.IsSet _value_i2) {_Host_i3 : Type v3} [_rep_i3 : Litex.Representation M _Host_i3] (_value_i3 : Litex.Obj (M := M) _Host_i3) (h_8 : Litex.IsSet _value_i3), (by
  let _object_w6 := (Litex.cart (M := M) ![Litex.denote _value_i1, Litex.denote _value_i2, Litex.denote _value_i3] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i2) (Fin.cases (Litex.isSet _value_i3) (fun i => Fin.elim0 i)))))
  let _object_w7 := (Litex.setBuilder (let _wd_1_0 := (let _wd_2_0 := (Litex.union _value_i1 _value_i2);
  let _wd_2_1 := _value_i3;
  (Litex.union _wd_2_0 _wd_2_1));
  let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.union _value_i1 _value_i2);
    let _wd_2_1 := _value_i3;
    (Litex.union _wd_2_0 _wd_2_1))
    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)))) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_23 : Litex.In _value_i4 (let _wd_1_0 := (let _wd_2_0 := (Litex.union _value_i1 _value_i2);
  let _wd_2_1 := _value_i3;
  (Litex.union _wd_2_0 _wd_2_1));
  let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.union _value_i1 _value_i2);
    let _wd_2_1 := _value_i3;
    (Litex.union _wd_2_0 _wd_2_1))
    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num))))) => (by
    let _object_h24 := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (let _wd_2_0 := (Litex.union _value_i1 _value_i2);
    let _wd_2_1 := _value_i3;
    (Litex.union _wd_2_0 _wd_2_1));
    let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
    (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.union _value_i1 _value_i2);
      let _wd_2_1 := _value_i3;
      (Litex.union _wd_2_0 _wd_2_1))
      exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num))))))
    have h_24 : Litex.In _value_i4 _object_h24 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inOfSame _value_i4 _value_i4 (let _wd_1_0 := (let _wd_2_0 := (Litex.union _value_i1 _value_i2);
            let _wd_2_1 := _value_i3;
            (Litex.union _wd_2_0 _wd_2_1));
            let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
            (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.union _value_i1 _value_i2);
              let _wd_2_1 := _value_i3;
              (Litex.union _wd_2_0 _wd_2_1))
              exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)))) _object_h24 (Litex.sameRefl _value_i4) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (let _wd_2_0 := (Litex.union _value_i1 _value_i2);
            let _wd_2_1 := _value_i3;
            (Litex.union _wd_2_0 _wd_2_1));
            let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
            (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.union _value_i1 _value_i2);
              let _wd_2_1 := _value_i3;
              (Litex.union _wd_2_0 _wd_2_1))
              exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num))))) h_23)
          )
      )
    exact ∃ (h_1 : Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
    Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
    let _wd_1_1 := _value_i3;
    (Litex.union _wd_1_0 _wd_1_1)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_24 (by
      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
      exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (3 : ℂ) (1 : ℂ) (1 : ℤ) (3 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) _value_i1), ∃ (h_2 : Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
    Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
    let _wd_1_1 := _value_i3;
    (Litex.union _wd_1_0 _wd_1_1)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_24 (by
      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
      exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (3 : ℂ) (2 : ℂ) (1 : ℤ) (3 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) _value_i2), Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (3 : ℂ));
    Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
    let _wd_1_1 := _value_i3;
    (Litex.union _wd_1_0 _wd_1_1)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_24 (by
      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
      exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (3 : ℂ) (3 : ℂ) (1 : ℤ) (3 : ℤ) (3 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) _value_i3
  )))
  exact (by
    let _equal_wd_1_0 := _object_w6
    let _equal_wd_1_1 := _object_w7
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_6 _Host_i2 _rep_i2 _value_i2 h_7 _Host_i3 _rep_i3 _value_i3 h_8
          let _object_w6 := (Litex.cart (M := M) ![Litex.denote _value_i1, Litex.denote _value_i2, Litex.denote _value_i3] (Fin.cases (Litex.isSet _value_i1) (Fin.cases (Litex.isSet _value_i2) (Fin.cases (Litex.isSet _value_i3) (fun i => Fin.elim0 i)))))
          let _object_w7 := (Litex.setBuilder (let _wd_1_0 := (let _wd_2_0 := (Litex.union _value_i1 _value_i2);
          let _wd_2_1 := _value_i3;
          (Litex.union _wd_2_0 _wd_2_1));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.union _value_i1 _value_i2);
            let _wd_2_1 := _value_i3;
            (Litex.union _wd_2_0 _wd_2_1))
            exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)))) (fun (_value_i4 : Litex.Obj (M := M) M.Value) (h_23 : Litex.In _value_i4 (let _wd_1_0 := (let _wd_2_0 := (Litex.union _value_i1 _value_i2);
          let _wd_2_1 := _value_i3;
          (Litex.union _wd_2_0 _wd_2_1));
          let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
          (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.union _value_i1 _value_i2);
            let _wd_2_1 := _value_i3;
            (Litex.union _wd_2_0 _wd_2_1))
            exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num))))) => (by
            let _object_h24 := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (let _wd_2_0 := (Litex.union _value_i1 _value_i2);
            let _wd_2_1 := _value_i3;
            (Litex.union _wd_2_0 _wd_2_1));
            let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
            (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.union _value_i1 _value_i2);
              let _wd_2_1 := _value_i3;
              (Litex.union _wd_2_0 _wd_2_1))
              exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num))))))
            have h_24 : Litex.In _value_i4 _object_h24 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inOfSame _value_i4 _value_i4 (let _wd_1_0 := (let _wd_2_0 := (Litex.union _value_i1 _value_i2);
                    let _wd_2_1 := _value_i3;
                    (Litex.union _wd_2_0 _wd_2_1));
                    let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
                    (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.union _value_i1 _value_i2);
                      let _wd_2_1 := _value_i3;
                      (Litex.union _wd_2_0 _wd_2_1))
                      exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num)))) _object_h24 (Litex.sameRefl _value_i4) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (let _wd_2_0 := (Litex.union _value_i1 _value_i2);
                    let _wd_2_1 := _value_i3;
                    (Litex.union _wd_2_0 _wd_2_1));
                    let _wd_1_1 := (Litex.number (M := M) (3 : ℂ));
                    (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := (let _wd_2_0 := (Litex.union _value_i1 _value_i2);
                      let _wd_2_1 := _value_i3;
                      (Litex.union _wd_2_0 _wd_2_1))
                      exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (3 : ℂ) (3 : ℕ) (by norm_num))))) h_23)
                  )
              )
            exact ∃ (h_1 : Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
            Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
            let _wd_1_1 := _value_i3;
            (Litex.union _wd_1_0 _wd_1_1)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_24 (by
              let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
              exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (3 : ℂ) (1 : ℂ) (1 : ℤ) (3 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) _value_i1), ∃ (h_2 : Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
            Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
            let _wd_1_1 := _value_i3;
            (Litex.union _wd_1_0 _wd_1_1)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_24 (by
              let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
              exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (3 : ℂ) (2 : ℂ) (1 : ℤ) (3 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) _value_i2), Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (3 : ℂ));
            Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num))) (let _wd_1_0 := (Litex.union _value_i1 _value_i2);
            let _wd_1_1 := _value_i3;
            (Litex.union _wd_1_0 _wd_1_1)) (fun (_litex_input : M.Value) => (fun (_raw_i5 : M.Value) => True) _litex_input) _value_i4 _litex_call_arg_0 h_24 (by
              let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (3 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (3 : ℂ) (3 : ℤ) (by norm_num)))
              exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (3 : ℂ) (3 : ℂ) (1 : ℤ) (3 : ℤ) (3 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) _value_i3
          )))
          have h_4 : (by
            let _equal_wd_1_0 := _object_w6
            let _equal_wd_1_1 := _object_w7
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w6;
                  let _equal_wd_1_1 := _object_w7;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from by
                    let _cart := _equal_wd_1_0
                    let _definition := _equal_wd_1_1
                    let _bound := _definition.val.bound
                    apply Litex.cartSameSetBuilder _cart _bound _definition.val.predicate (Litex.denote _bound.val.carrier)
                    · exact Litex.denoteFiniteSeq _bound 3 (by change M.number (3 : ℂ) = M.number ((3 : ℕ) : ℂ); norm_num)
                    · exact (by
                    have _finiteProof_0 := ((show ∀ x, M.mem x (_cart.val.factors (0 : Fin 3)) → M.mem x (Litex.denote _bound.val.carrier) from fun _x _hx => (Litex.SetSemantics.union_members (M := M) _ _ _).mpr (Or.inl ((Litex.SetSemantics.union_members (M := M) _ _ _).mpr (Or.inl (_hx))))))
                    have _finiteProof_1 := ((show ∀ x, M.mem x (_cart.val.factors (1 : Fin 3)) → M.mem x (Litex.denote _bound.val.carrier) from fun _x _hx => (Litex.SetSemantics.union_members (M := M) _ _ _).mpr (Or.inl ((Litex.SetSemantics.union_members (M := M) _ _ _).mpr (Or.inr (_hx))))))
                    have _finiteProof_2 := ((show ∀ x, M.mem x (_cart.val.factors (2 : Fin 3)) → M.mem x (Litex.denote _bound.val.carrier) from fun _x _hx => (Litex.SetSemantics.union_members (M := M) _ _ _).mpr (Or.inr (_hx))))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (Fin.cases _finiteProof_2 (fun i => Fin.elim0 i))))
                  )
                    · intro _point _hin
                      change (∃ _ : (M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _point) (M.number (1 : ℂ))) (_cart.val.factors (0 : Fin 3))), ∃ _ : (M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _point) (M.number (2 : ℂ))) (_cart.val.factors (1 : Fin 3))), M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _point) (M.number (3 : ℂ))) (_cart.val.factors (2 : Fin 3))) ↔ _
                      constructor
                      · rintro ⟨_coord_0, _coord_1, _coord_2⟩
                        exact (by
                    have _finiteProof_0 := ((show M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _point) (Litex.FiniteFunction.index (0 : Fin 3))) (_cart.val.factors (0 : Fin 3)) from by
                      have _index : Litex.FiniteFunction.index (M := M) (0 : Fin 3) = M.number (1 : ℂ) := by norm_num [Litex.FiniteFunction.index]
                      rw [_index]
                      exact _coord_0))
                    have _finiteProof_1 := ((show M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _point) (Litex.FiniteFunction.index (1 : Fin 3))) (_cart.val.factors (1 : Fin 3)) from by
                      have _index : Litex.FiniteFunction.index (M := M) (1 : Fin 3) = M.number (2 : ℂ) := by norm_num [Litex.FiniteFunction.index]
                      rw [_index]
                      exact _coord_1))
                    have _finiteProof_2 := ((show M.mem (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _point) (Litex.FiniteFunction.index (2 : Fin 3))) (_cart.val.factors (2 : Fin 3)) from by
                      have _index : Litex.FiniteFunction.index (M := M) (2 : Fin 3) = M.number (3 : ℂ) := by norm_num [Litex.FiniteFunction.index]
                      rw [_index]
                      exact _coord_2))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (Fin.cases _finiteProof_2 (fun i => Fin.elim0 i))))
                  )
                      · intro _all
                        exact ⟨(by
                    have _index : Litex.FiniteFunction.index (M := M) (0 : Fin 3) = M.number (1 : ℂ) := by norm_num [Litex.FiniteFunction.index]
                    rw [← _index]
                    exact _all (0 : Fin 3)), (by
                    have _index : Litex.FiniteFunction.index (M := M) (1 : Fin 3) = M.number (2 : ℂ) := by norm_num [Litex.FiniteFunction.index]
                    rw [← _index]
                    exact _all (1 : Fin 3)), (by
                    have _index : Litex.FiniteFunction.index (M := M) (2 : Fin 3) = M.number (3 : ℂ) := by norm_num [Litex.FiniteFunction.index]
                    rw [← _index]
                    exact _all (2 : Fin 3))⟩)))
                )
            )
          exact h_4
        )
      )
  )

theorem h_112 : ∀ {_Host_i8 : Type v8} [_rep_i8 : Litex.Representation M _Host_i8] (_value_i8 : Litex.Obj (M := M) _Host_i8) (h_113 : Litex.IsSet _value_i8) {_Host_i9 : Type v9} [_rep_i9 : Litex.Representation M _Host_i9] (_value_i9 : Litex.Obj (M := M) _Host_i9) (h_114 : Litex.IsSet _value_i9), (by
  let _object_w12 := (Litex.setBuilder (let _wd_1_0 := (Litex.union _value_i8 _value_i9);
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.union _value_i8 _value_i9)
    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (fun (_value_i10 : Litex.Obj (M := M) M.Value) (h_125 : Litex.In _value_i10 (let _wd_1_0 := (Litex.union _value_i8 _value_i9);
  let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
  (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.union _value_i8 _value_i9)
    exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) => (by
    let _object_h126 := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (Litex.union _value_i8 _value_i9);
    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
    (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
      let _atomic_wd_1_0 := (Litex.union _value_i8 _value_i9)
      exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))
    have h_126 : Litex.In _value_i10 _object_h126 :=
      (by
        litex_checked_step =>
          exact (
            (Litex.inOfSame _value_i10 _value_i10 (let _wd_1_0 := (Litex.union _value_i8 _value_i9);
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := (Litex.union _value_i8 _value_i9)
              exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) _object_h126 (Litex.sameRefl _value_i10) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (Litex.union _value_i8 _value_i9);
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := (Litex.union _value_i8 _value_i9)
              exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) h_125)
          )
      )
    exact ∃ (h_109 : Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
    Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union _value_i8 _value_i9) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input) _value_i10 _litex_call_arg_0 h_126 (by
      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
      exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) _value_i8), Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
    Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union _value_i8 _value_i9) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input) _value_i10 _litex_call_arg_0 h_126 (by
      let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
      exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) _value_i9
  )))
  let _object_w13 := (Litex.cart (M := M) ![Litex.denote _value_i8, Litex.denote _value_i9] (Fin.cases (Litex.isSet _value_i8) (Fin.cases (Litex.isSet _value_i9) (fun i => Fin.elim0 i))))
  exact (by
    let _equal_wd_1_0 := _object_w12
    let _equal_wd_1_1 := _object_w13
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i8 _rep_i8 _value_i8 h_113 _Host_i9 _rep_i9 _value_i9 h_114
          let _object_w12 := (Litex.setBuilder (let _wd_1_0 := (Litex.union _value_i8 _value_i9);
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.union _value_i8 _value_i9)
            exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (fun (_value_i10 : Litex.Obj (M := M) M.Value) (h_125 : Litex.In _value_i10 (let _wd_1_0 := (Litex.union _value_i8 _value_i9);
          let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
          (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.union _value_i8 _value_i9)
            exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) => (by
            let _object_h126 := (Litex.fnSet (Litex.finiteSeqSignature (let _wd_1_0 := (Litex.union _value_i8 _value_i9);
            let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
            (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
              let _atomic_wd_1_0 := (Litex.union _value_i8 _value_i9)
              exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))))
            have h_126 : Litex.In _value_i10 _object_h126 :=
              (by
                litex_checked_step =>
                  exact (
                    (Litex.inOfSame _value_i10 _value_i10 (let _wd_1_0 := (Litex.union _value_i8 _value_i9);
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := (Litex.union _value_i8 _value_i9)
                      exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) _object_h126 (Litex.sameRefl _value_i10) (Litex.finiteSeq_eq_fnSet (let _wd_1_0 := (Litex.union _value_i8 _value_i9);
                    let _wd_1_1 := (Litex.number (M := M) (2 : ℂ));
                    (Litex.finiteSeq _wd_1_0 _wd_1_1 (by
                      let _atomic_wd_1_0 := (Litex.union _value_i8 _value_i9)
                      exact (Litex.isSet _atomic_wd_1_0)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) h_125)
                  )
              )
            exact ∃ (h_109 : Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
            Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union _value_i8 _value_i9) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input) _value_i10 _litex_call_arg_0 h_126 (by
              let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
              exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) _value_i8), Litex.In (let _litex_call_arg_0 := (Litex.number (M := M) (2 : ℂ));
            Litex.callOnDomain (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))) (Litex.union _value_i8 _value_i9) (fun (_litex_input : M.Value) => (fun (_raw_i11 : M.Value) => True) _litex_input) _value_i10 _litex_call_arg_0 h_126 (by
              let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
              exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) True.intro) _value_i9
          )))
          let _object_w13 := (Litex.cart (M := M) ![Litex.denote _value_i8, Litex.denote _value_i9] (Fin.cases (Litex.isSet _value_i8) (Fin.cases (Litex.isSet _value_i9) (fun i => Fin.elim0 i))))
          have h_111 : (by
            let _equal_wd_1_0 := _object_w12
            let _equal_wd_1_1 := _object_w13
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w12;
                  let _equal_wd_1_1 := _object_w13;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from ((show Litex.Same _equal_wd_1_1 _equal_wd_1_0 from by
                    let _cart := _equal_wd_1_1
                    let _definition := _equal_wd_1_0
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
                    exact _all (1 : Fin 2))⟩)).symm))
                )
            )
          exact h_111
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_generic_x5f_cartesian_x5f_definitions_x2f_statement_x2e_lit
