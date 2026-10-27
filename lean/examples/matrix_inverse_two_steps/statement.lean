import Litex

set_option linter.unusedVariables false

namespace LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_inverse_x5f_two_x5f_steps_x2f_statement_x2e_lit

universe u v1
variable {M : Litex.Semantics.{u}}
set_option linter.unusedSectionVars false
variable [_functionSemantics : Litex.FunctionSemantics M]

theorem h_5 : ∀ {_Host_i1 : Type v1} [_rep_i1 : Litex.Representation M _Host_i1] (_value_i1 : Litex.Obj (M := M) _Host_i1) (h_39 : Litex.In _value_i1 (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))) (h_1 : (by
  let _atomic_wd_1_0 := (Litex.matrixDeterminant _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (by
    let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
    exact h_39))
  exact ¬ Litex.Same _atomic_wd_1_0 (Litex.number (M := M) (0 : ℂ)))), (by
  let _object_h40 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))))
  have h_40 : Litex.In _value_i1 _object_h40 :=
    (by
      litex_checked_step =>
        exact (
          (Litex.inOfSame _value_i1 _value_i1 (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))) _object_h40 (Litex.sameRefl _value_i1) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) h_39)
        )
    )
  let _object_w55 := (let _litex_matrix_head := (Litex.matrixInverse _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
    exact h_39) (by
    let _atomic_wd_1_0 := (Litex.matrixDeterminant _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (by
      let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
      exact h_39))
    exact h_1));
  (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
  let _litex_call_arg_1 := (Litex.number (M := M) (2 : ℂ));
  Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.order (_litex_matrix_head).val.order .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixInverseInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))), True.intro⟩)))
  let _object_w56 := (let _wd_1_0 := (Litex.matrixCofactor _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInNPosOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num) (by norm_num)) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
    exact h_39));
  let _wd_1_1 := (Litex.matrixDeterminant _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
    exact h_39));
  (Litex.div _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := (Litex.matrixCofactor _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInNPosOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num) (by norm_num)) (by
      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
      exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
      let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
      exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (by
      let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
      exact h_39))
    exact (Litex.matrixCofactorInC _atomic_wd_1_0)) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.matrixDeterminantInC _atomic_wd_1_0)) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact h_1)))
  let _object_w57 := (Litex.matrixCofactor _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInNPosOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num) (by norm_num)) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (by
    let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
    exact h_39))
  let _object_w58 := (let _wd_1_0 := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
  let _litex_call_arg_1 := (Litex.number (M := M) (2 : ℂ));
  Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))] (by
    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))
    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))
    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
  )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i1 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_40 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))) True.intro);
  (Litex.neg _wd_1_0 (by
    let _atomic_wd_1_0 := _wd_1_0
    exact (by
      let _litex_return_call := _atomic_wd_1_0
      exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
  let _object_w59 := (let _wd_1_0 := _object_w58;
  let _wd_1_1 := (_object_w56).val.right;
  (Litex.div _wd_1_0 _wd_1_1 (by
    let _atomic_wd_1_0 := _object_w58
    exact (by
      let _arithmetic := _atomic_wd_1_0
      exact Litex.negInC _arithmetic.val.arg _arithmetic.wd)) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact (Litex.matrixDeterminantInC _atomic_wd_1_0)) (by
    let _atomic_wd_1_0 := _wd_1_1
    exact h_1)))
  exact (((by
    let _equal_wd_1_0 := _object_w55
    let _equal_wd_1_1 := _object_w56
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((((by
    let _equal_wd_1_0 := _object_w57
    let _equal_wd_1_1 := _object_w58
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)) ∧ ((by
    let _equal_wd_1_0 := _object_w55
    let _equal_wd_1_1 := _object_w59
    exact Litex.Same _equal_wd_1_0 _equal_wd_1_1)))))
) :=
  (by
    litex_complete =>
      exact (
        (by
          intro _Host_i1 _rep_i1 _value_i1 h_39 h_1
          let _object_h40 := (Litex.fnSet (Litex.matrixSignature (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))))
          have h_40 : Litex.In _value_i1 _object_h40 :=
            (by
              litex_checked_step =>
                exact (
                  (Litex.inOfSame _value_i1 _value_i1 (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))) _object_h40 (Litex.sameRefl _value_i1) ((show @Eq M.Value _ _ from Eq.refl _).trans (Litex.matrixSet_eq_fnSet (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num))))) h_39)
                )
            )
          let _object_w55 := (let _litex_matrix_head := (Litex.matrixInverse _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
            exact h_39) (by
            let _atomic_wd_1_0 := (Litex.matrixDeterminant _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (by
              let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
              exact h_39))
            exact h_1));
          (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
          let _litex_call_arg_1 := (Litex.number (M := M) (2 : ℂ));
          Litex.callOn (Litex.matrixEntrywiseSignature (_litex_matrix_head).val.order (_litex_matrix_head).val.order .complex) _litex_matrix_head (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) (Litex.matrixInverseInFnSet _litex_matrix_head) ((Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨(Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))), True.intro⟩)))
          let _object_w56 := (let _wd_1_0 := (Litex.matrixCofactor _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInNPosOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num) (by norm_num)) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
            exact h_39));
          let _wd_1_1 := (Litex.matrixDeterminant _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
            exact h_39));
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := (Litex.matrixCofactor _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInNPosOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num) (by norm_num)) (by
              let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
              exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
              let _atomic_wd_2_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
              exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (by
              let _atomic_wd_2_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
              exact h_39))
            exact (Litex.matrixCofactorInC _atomic_wd_1_0)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.matrixDeterminantInC _atomic_wd_1_0)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact h_1)))
          have h_2 : (by
            let _equal_wd_1_0 := _object_w55
            let _equal_wd_1_1 := _object_w56
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w55;
                  let _equal_wd_1_1 := _object_w56;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (((show Litex.denote _equal_wd_1_0 = (M.divValue (Litex.matrixCofactorValue (Litex.denote ((_equal_wd_1_0).val.function).val.matrix) ((_equal_wd_1_0).val.function).val.order (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.number (M := M) (1 : ℂ)))) (Litex.matrixDeterminantValue (Litex.denote ((_equal_wd_1_0).val.function).val.matrix) ((_equal_wd_1_0).val.function).val.order)) from by
                    have h := (congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f (Litex.denote (Litex.callArguments2 (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ))))) (show @Eq M.Value _ _ from Eq.refl _)).trans (Litex.matrixInverseCall (_equal_wd_1_0).val.function (Litex.denote (Litex.callArguments2 (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)))) ((Litex.SetSemantics.sep_members (M := M) (Litex.denote (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))] (by
                    have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))
                    have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))
                    exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
                  ))) (fun (_litex_input : M.Value) => (fun (_raw_i36 : M.Value) (_raw_i37 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) (Litex.denote (Litex.callArguments2 (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ))))).mpr ⟨(Litex.callArguments2_mem_cart (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
                    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
                    let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
                    exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))), True.intro⟩))
                    change Litex.denote _equal_wd_1_0 = Litex.matrixInverseBody (Litex.denote ((_equal_wd_1_0).val.function).val.matrix) ((_equal_wd_1_0).val.function).val.order (Litex.FiniteFunction.pack2 (Litex.denote (Litex.number (M := M) (1 : ℂ))) (Litex.denote (Litex.number (M := M) (2 : ℂ)))) at h
                    unfold Litex.matrixInverseBody Litex.matrixAdjugateBody at h
                    rw [Litex.FiniteFunction.unpack_pack2] at h
                    exact h).trans (show (M.divValue (Litex.matrixCofactorValue (Litex.denote ((_equal_wd_1_0).val.function).val.matrix) ((_equal_wd_1_0).val.function).val.order (Litex.denote (Litex.number (M := M) (2 : ℂ))) (Litex.denote (Litex.number (M := M) (1 : ℂ)))) (Litex.matrixDeterminantValue (Litex.denote ((_equal_wd_1_0).val.function).val.matrix) ((_equal_wd_1_0).val.function).val.order)) = (Litex.denote _equal_wd_1_1) from rfl)).trans (show @Eq M.Value _ _ from Eq.refl _))))
                )
            )
          let _object_w57 := (Litex.matrixCofactor _value_i1 (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (1 : ℂ)) (Litex.numberInNPosOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num) (by norm_num)) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (by
            let _atomic_wd_1_1 := (Litex.matrixSet (Litex.C (M := M)) (Litex.number (M := M) (2 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.isSet (Litex.C (M := M))) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)) (Litex.NativeBridge.numberInNOfEq (M := M) (2 : ℂ) (2 : ℕ) (by norm_num)))
            exact h_39))
          let _object_w58 := (let _wd_1_0 := (let _litex_call_arg_0 := (Litex.number (M := M) (1 : ℂ));
          let _litex_call_arg_1 := (Litex.number (M := M) (2 : ℂ));
          Litex.callOnDomain (Litex.cart (M := M) ![(Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))), (Litex.denote (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))] (by
            have _finiteProof_0 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))
            have _finiteProof_1 := (Litex.isSet (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num))))
            exact (Fin.cases _finiteProof_0 (Fin.cases _finiteProof_1 (fun i => Fin.elim0 i)))
          )) (Litex.C (M := M)) (fun (_litex_input : M.Value) => (fun (_raw_i2 : M.Value) (_raw_i3 : M.Value) => True) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (1 : ℂ))) (Litex.FunctionSemantics.callValue (M := M) _litex_input (M.number (2 : ℂ)))) _value_i1 (Litex.callArguments2 _litex_call_arg_0 _litex_call_arg_1) h_40 (Litex.callArguments2_mem_cart _litex_call_arg_0 _litex_call_arg_1 (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (1 : ℂ) (1 : ℤ) (2 : ℤ) (1 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))) (by
            let _atomic_wd_1_1 := (Litex.closedRange (Litex.number (M := M) (1 : ℂ)) (Litex.number (M := M) (2 : ℂ)) (Litex.NativeBridge.numberInZOfEq (M := M) (1 : ℂ) (1 : ℤ) (by norm_num)) (Litex.NativeBridge.numberInZOfEq (M := M) (2 : ℂ) (2 : ℤ) (by norm_num)))
            exact (Litex.numberInClosedRangeOfEq (M := M) (1 : ℂ) (2 : ℂ) (2 : ℂ) (1 : ℤ) (2 : ℤ) (2 : ℤ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))) True.intro);
          (Litex.neg _wd_1_0 (by
            let _atomic_wd_1_0 := _wd_1_0
            exact (by
              let _litex_return_call := _atomic_wd_1_0
              exact Litex.inOfSame _litex_return_call _litex_return_call (Litex.C (M := M)) (Litex.C (M := M)) (Litex.sameRefl _litex_return_call) (Litex.sameRefl (Litex.C (M := M))) (Litex.callOnInOutput _litex_return_call)))))
          have h_3 : (by
            let _equal_wd_1_0 := _object_w57
            let _equal_wd_1_1 := _object_w58
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w57;
                  let _equal_wd_1_1 := _object_w58;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (by
                    let _cofactor := _equal_wd_1_0
                    let _expanded := _equal_wd_1_1
                    have _definition : Litex.Same _cofactor _expanded := by
                      have _raw := Litex.matrixCofactorTwo21 (Litex.denote _cofactor.val.matrix) _cofactor.wd.2.2.2.2
                      simp only [Litex.matrixEntryValue, Nat.cast_one, Nat.cast_ofNat] at _raw
                      exact _raw
                    exact (_definition.trans (show @Eq M.Value _ _ from Eq.refl _))
                  )))
                )
            )
          let _object_w59 := (let _wd_1_0 := _object_w58;
          let _wd_1_1 := (_object_w56).val.right;
          (Litex.div _wd_1_0 _wd_1_1 (by
            let _atomic_wd_1_0 := _object_w58
            exact (by
              let _arithmetic := _atomic_wd_1_0
              exact Litex.negInC _arithmetic.val.arg _arithmetic.wd)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact (Litex.matrixDeterminantInC _atomic_wd_1_0)) (by
            let _atomic_wd_1_0 := _wd_1_1
            exact h_1)))
          have h_4 : (by
            let _equal_wd_1_0 := _object_w55
            let _equal_wd_1_1 := _object_w59
            exact Litex.Same _equal_wd_1_0 _equal_wd_1_1) :=
            (by
              litex_checked_step =>
                exact (
                  (let _equal_wd_1_0 := _object_w55;
                  let _equal_wd_1_1 := _object_w59;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_1_1 from (let _equal_wd_2_0 := _object_w56;
                  let _equal_wd_2_1 := _equal_wd_1_1;
                  (show Litex.Same _equal_wd_1_0 _equal_wd_2_1 from (Eq.trans h_2 (Eq.trans (congrArg₂ M.divValue (show (Litex.denote _object_w57) = (M.negValue (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _value_i1) (Litex.FiniteFunction.tupleValue (M := M) ![(M.number (1 : ℂ)), (M.number (2 : ℂ))]))) from h_3) (show (Litex.denote (_equal_wd_2_1).val.right) = (Litex.denote (_equal_wd_2_1).val.right) from (show @Eq M.Value _ _ from Eq.refl _))) (show @Eq M.Value _ _ from Eq.refl _)))))))
                )
            )
          exact (And.intro h_2 (And.intro h_3 h_4))
        )
      )
  )
end LitexCompiled.file_lean_x2f_examples_x2f_matrix_x5f_inverse_x5f_two_x5f_steps_x2f_statement_x2e_lit
